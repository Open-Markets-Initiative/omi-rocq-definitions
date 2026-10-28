From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Financial Industry Regulatory Authority Bulletin Board Dissemination Service

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
      - a field present only on a condition
      - a length prefix framing what follows
  *)

Module FinraOtcBbdsV20181A.

  Module Datetime.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End Datetime.

  Module MessageHeader.

    (** Message Header *)
    Record t := {
      session_identifier : list byte;
      retransmission_requester : list byte;
      message_sequence_number : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_identifier record) = 1 /\
      Datatypes.length (retransmission_requester record) = 2 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime.bounded (datetime record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (session_identifier record) ++
      encode_bytes 2 (retransmission_requester record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime.encode (datetime record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (session_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retransmission_requester_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (message_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_center_originator_id_value, bytes) =>
                      match Datetime.decode bytes with
                      | None => None
                      | Some (datetime_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| session_identifier := session_identifier_value; retransmission_requester := retransmission_requester_value; message_sequence_number := message_sequence_number_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime.encode_length. reflexivity.
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
      rewrite Datetime.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime.eq_dec]. Defined.

  End MessageHeader.

  Module Datetime2.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End Datetime2.

  Module MessageHeader2.

    (** Message Header *)
    Record t := {
      session_identifier : list byte;
      retransmission_requester : list byte;
      message_sequence_number : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime2.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_identifier record) = 1 /\
      Datatypes.length (retransmission_requester record) = 2 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime2.bounded (datetime record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (session_identifier record) ++
      encode_bytes 2 (retransmission_requester record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime2.encode (datetime record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (session_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retransmission_requester_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (message_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_center_originator_id_value, bytes) =>
                      match Datetime2.decode bytes with
                      | None => None
                      | Some (datetime_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| session_identifier := session_identifier_value; retransmission_requester := retransmission_requester_value; message_sequence_number := message_sequence_number_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime2.encode_length. reflexivity.
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
      rewrite Datetime2.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime2.eq_dec]. Defined.

  End MessageHeader2.

  Module ActionDatetime.

    (** Action Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End ActionDatetime.

  Module TradingActionMessage.

    (** FINRA will disseminate this message to inform customers of trading actions, such as halts or trading resumptions which affect individual OTCBB or Other OTC securities *)
    Record t := {
      message_header : MessageHeader2.t;
      stock_symbol : list byte;
      action : list byte;
      action_datetime : ActionDatetime.t;
      reason_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader2.bounded (message_header record) /\
      Datatypes.length (stock_symbol record) = 11 /\
      Datatypes.length (action record) = 1 /\
      ActionDatetime.bounded (action_datetime record) /\
      Datatypes.length (reason_code record) = 6.

    Definition encode (record : t) : list byte :=
      MessageHeader2.encode (message_header record) ++
      encode_bytes 11 (stock_symbol record) ++
      encode_bytes 1 (action record) ++
      ActionDatetime.encode (action_datetime record) ++
      encode_bytes 6 (reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader2.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (stock_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (action_value, bytes) =>
                  match ActionDatetime.decode bytes with
                  | None => None
                  | Some (action_datetime_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (reason_code_value, bytes) =>
                          Some ({| message_header := message_header_value; stock_symbol := stock_symbol_value; action := action_value; action_datetime := action_datetime_value; reason_code := reason_code_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader2.encode_length, !encode_bytes_length, !ActionDatetime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader2.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite ActionDatetime.decode_encode by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader2.eq_dec | apply ActionDatetime.eq_dec]. Defined.

  End TradingActionMessage.

  Module Datetime3.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End Datetime3.

  Module MessageHeader3.

    (** Message Header *)
    Record t := {
      session_identifier : list byte;
      retransmission_requester : list byte;
      message_sequence_number : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime3.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_identifier record) = 1 /\
      Datatypes.length (retransmission_requester record) = 2 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime3.bounded (datetime record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (session_identifier record) ++
      encode_bytes 2 (retransmission_requester record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime3.encode (datetime record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (session_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retransmission_requester_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (message_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_center_originator_id_value, bytes) =>
                      match Datetime3.decode bytes with
                      | None => None
                      | Some (datetime_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| session_identifier := session_identifier_value; retransmission_requester := retransmission_requester_value; message_sequence_number := message_sequence_number_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime3.encode_length. reflexivity.
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
      rewrite Datetime3.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime3.eq_dec]. Defined.

  End MessageHeader3.

  Module StartOfDayMessage.

    (** The Start of Day control message signifies the beginning of each operational cycle for TDDS processing *)
    Record t := {
      message_header : MessageHeader3.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader3.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader3.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader3.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader3.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader3.eq_dec]. Defined.

  End StartOfDayMessage.

  Module Datetime4.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End Datetime4.

  Module MessageHeader4.

    (** Message Header *)
    Record t := {
      session_identifier : list byte;
      retransmission_requester : list byte;
      message_sequence_number : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime4.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_identifier record) = 1 /\
      Datatypes.length (retransmission_requester record) = 2 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime4.bounded (datetime record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (session_identifier record) ++
      encode_bytes 2 (retransmission_requester record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime4.encode (datetime record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (session_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retransmission_requester_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (message_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_center_originator_id_value, bytes) =>
                      match Datetime4.decode bytes with
                      | None => None
                      | Some (datetime_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| session_identifier := session_identifier_value; retransmission_requester := retransmission_requester_value; message_sequence_number := message_sequence_number_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime4.encode_length. reflexivity.
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
      rewrite Datetime4.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime4.eq_dec]. Defined.

  End MessageHeader4.

  Module EndOfDayMessage.

    (** The End of Day control message signals the end of active message dissemination for the TDDS operational cycle *)
    Record t := {
      message_header : MessageHeader4.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader4.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader4.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader4.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader4.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader4.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader4.eq_dec]. Defined.

  End EndOfDayMessage.

  Module Datetime5.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End Datetime5.

  Module MessageHeader5.

    (** Message Header *)
    Record t := {
      session_identifier : list byte;
      retransmission_requester : list byte;
      message_sequence_number : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime5.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_identifier record) = 1 /\
      Datatypes.length (retransmission_requester record) = 2 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime5.bounded (datetime record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (session_identifier record) ++
      encode_bytes 2 (retransmission_requester record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime5.encode (datetime record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (session_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retransmission_requester_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (message_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_center_originator_id_value, bytes) =>
                      match Datetime5.decode bytes with
                      | None => None
                      | Some (datetime_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| session_identifier := session_identifier_value; retransmission_requester := retransmission_requester_value; message_sequence_number := message_sequence_number_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime5.encode_length. reflexivity.
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
      rewrite Datetime5.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime5.eq_dec]. Defined.

  End MessageHeader5.

  Module MarketSessionOpenMessage.

    (** The Market Session Open Control Message signifies the opening of FINRA’s market systems for the session indicated in the Message Header *)
    Record t := {
      message_header : MessageHeader5.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader5.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader5.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader5.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader5.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader5.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader5.eq_dec]. Defined.

  End MarketSessionOpenMessage.

  Module Datetime6.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End Datetime6.

  Module MessageHeader6.

    (** Message Header *)
    Record t := {
      session_identifier : list byte;
      retransmission_requester : list byte;
      message_sequence_number : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime6.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_identifier record) = 1 /\
      Datatypes.length (retransmission_requester record) = 2 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime6.bounded (datetime record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (session_identifier record) ++
      encode_bytes 2 (retransmission_requester record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime6.encode (datetime record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (session_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retransmission_requester_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (message_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_center_originator_id_value, bytes) =>
                      match Datetime6.decode bytes with
                      | None => None
                      | Some (datetime_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| session_identifier := session_identifier_value; retransmission_requester := retransmission_requester_value; message_sequence_number := message_sequence_number_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime6.encode_length. reflexivity.
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
      rewrite Datetime6.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime6.eq_dec]. Defined.

  End MessageHeader6.

  Module MarketSessionCloseMessage.

    (** The Session Close Control Message signals the closing of FINRA’s market systems for the session indicated in the Message Header *)
    Record t := {
      message_header : MessageHeader6.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader6.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader6.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader6.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader6.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader6.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader6.eq_dec]. Defined.

  End MarketSessionCloseMessage.

  Module Datetime7.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End Datetime7.

  Module MessageHeader7.

    (** Message Header *)
    Record t := {
      session_identifier : list byte;
      retransmission_requester : list byte;
      message_sequence_number : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime7.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_identifier record) = 1 /\
      Datatypes.length (retransmission_requester record) = 2 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime7.bounded (datetime record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (session_identifier record) ++
      encode_bytes 2 (retransmission_requester record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime7.encode (datetime record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (session_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retransmission_requester_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (message_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_center_originator_id_value, bytes) =>
                      match Datetime7.decode bytes with
                      | None => None
                      | Some (datetime_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| session_identifier := session_identifier_value; retransmission_requester := retransmission_requester_value; message_sequence_number := message_sequence_number_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime7.encode_length. reflexivity.
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
      rewrite Datetime7.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime7.eq_dec]. Defined.

  End MessageHeader7.

  Module EndOfRetransmissionRequestsMessage.

    (** This message signals that no further retransmission requests will be honored. The End of Retransmission Requests message will be sent three times, at one-minute intervals *)
    Record t := {
      message_header : MessageHeader7.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader7.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader7.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader7.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader7.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader7.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader7.eq_dec]. Defined.

  End EndOfRetransmissionRequestsMessage.

  Module Datetime8.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End Datetime8.

  Module MessageHeader8.

    (** Message Header *)
    Record t := {
      session_identifier : list byte;
      retransmission_requester : list byte;
      message_sequence_number : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime8.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_identifier record) = 1 /\
      Datatypes.length (retransmission_requester record) = 2 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime8.bounded (datetime record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (session_identifier record) ++
      encode_bytes 2 (retransmission_requester record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime8.encode (datetime record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (session_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retransmission_requester_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (message_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_center_originator_id_value, bytes) =>
                      match Datetime8.decode bytes with
                      | None => None
                      | Some (datetime_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| session_identifier := session_identifier_value; retransmission_requester := retransmission_requester_value; message_sequence_number := message_sequence_number_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime8.encode_length. reflexivity.
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
      rewrite Datetime8.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime8.eq_dec]. Defined.

  End MessageHeader8.

  Module EndOfTransmissionsMessage.

    (** The End of Transmissions Message signals that there will be no further transmissions of data sent through the TDDS line. *)
    Record t := {
      message_header : MessageHeader8.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader8.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader8.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader8.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader8.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader8.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader8.eq_dec]. Defined.

  End EndOfTransmissionsMessage.

  Module Datetime9.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End Datetime9.

  Module MessageHeader9.

    (** Message Header *)
    Record t := {
      session_identifier : list byte;
      retransmission_requester : list byte;
      message_sequence_number : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime9.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_identifier record) = 1 /\
      Datatypes.length (retransmission_requester record) = 2 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime9.bounded (datetime record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (session_identifier record) ++
      encode_bytes 2 (retransmission_requester record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime9.encode (datetime record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (session_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retransmission_requester_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (message_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_center_originator_id_value, bytes) =>
                      match Datetime9.decode bytes with
                      | None => None
                      | Some (datetime_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| session_identifier := session_identifier_value; retransmission_requester := retransmission_requester_value; message_sequence_number := message_sequence_number_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime9.encode_length. reflexivity.
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
      rewrite Datetime9.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime9.eq_dec]. Defined.

  End MessageHeader9.

  Module LineIntegrityMessage.

    (** The Line Integrity Control Message will be transmitted at approximately one-minute intervals to verify the operational integrity of the TDDS message transmission, and will be intermixed with other messages *)
    Record t := {
      message_header : MessageHeader9.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader9.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader9.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader9.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader9.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader9.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader9.eq_dec]. Defined.

  End LineIntegrityMessage.

  Module Datetime10.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End Datetime10.

  Module MessageHeader10.

    (** Message Header *)
    Record t := {
      session_identifier : list byte;
      retransmission_requester : list byte;
      message_sequence_number : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime10.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_identifier record) = 1 /\
      Datatypes.length (retransmission_requester record) = 2 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime10.bounded (datetime record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (session_identifier record) ++
      encode_bytes 2 (retransmission_requester record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime10.encode (datetime record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (session_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retransmission_requester_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (message_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_center_originator_id_value, bytes) =>
                      match Datetime10.decode bytes with
                      | None => None
                      | Some (datetime_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| session_identifier := session_identifier_value; retransmission_requester := retransmission_requester_value; message_sequence_number := message_sequence_number_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime10.encode_length. reflexivity.
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
      rewrite Datetime10.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime10.eq_dec]. Defined.

  End MessageHeader10.

  Module SequenceNumberResetMessage.

    (** The Sequence Number Reset Message forces the resetting of the Sequence Number. The Sequence Number will either be reset to zero or to a number greater than the last number previously transmitted *)
    Record t := {
      message_header : MessageHeader10.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader10.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader10.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader10.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader10.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader10.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader10.eq_dec]. Defined.

  End SequenceNumberResetMessage.

  Module Datetime11.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 2 /\
      Datatypes.length (month record) = 1 /\
      Datatypes.length (day record) = 1 /\
      Datatypes.length (hour record) = 1 /\
      Datatypes.length (minute record) = 1 /\
      Datatypes.length (second record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (year record) ++
      encode_bytes 1 (month record) ++
      encode_bytes 1 (day record) ++
      encode_bytes 1 (hour record) ++
      encode_bytes 1 (minute record) ++
      encode_bytes 1 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End Datetime11.

  Module MessageHeader11.

    (** Message Header *)
    Record t := {
      session_identifier : list byte;
      retransmission_requester : list byte;
      message_sequence_number : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime11.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_identifier record) = 1 /\
      Datatypes.length (retransmission_requester record) = 2 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime11.bounded (datetime record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (session_identifier record) ++
      encode_bytes 2 (retransmission_requester record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime11.encode (datetime record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (session_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retransmission_requester_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (message_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_center_originator_id_value, bytes) =>
                      match Datetime11.decode bytes with
                      | None => None
                      | Some (datetime_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| session_identifier := session_identifier_value; retransmission_requester := retransmission_requester_value; message_sequence_number := message_sequence_number_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime11.encode_length. reflexivity.
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
      rewrite Datetime11.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime11.eq_dec]. Defined.

  End MessageHeader11.

  Module EndOfTradeReportingMessage.

    (** The End of Trade Reporting Control Message signals that the ORF system is closed for market participant trade transactions *)
    Record t := {
      message_header : MessageHeader11.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader11.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader11.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader11.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader11.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader11.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader11.eq_dec]. Defined.

  End EndOfTradeReportingMessage.

End FinraOtcBbdsV20181A.
