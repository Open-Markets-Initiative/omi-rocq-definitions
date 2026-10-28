From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Financial Industry Regulatory Authority Trade Data Dissemination Service

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
      - a length prefix framing what follows
  *)

Module FinraOrfTddsV21.

  Module PacketHeader.

    Record t := {
      session : list byte;
      sequence : N;
      count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence record < 256 ^ N.of_nat 8)%N /\
      (count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 8 (sequence record) ++
      encode_uint 2 (count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sequence_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (count_value, bytes) =>
                  Some ({| session := session_value; sequence := sequence_value; count := count_value |}, bytes)
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

  Module MoldUdp64.

    (** Mold Udp64 Dfi Message Header *)
    Record t := {
      length_ : N;
      message_category : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_category record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_bytes 1 (message_category record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_category_value, bytes) =>
              Some ({| length_ := length__value; message_category := message_category_value |}, bytes)
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

  End MoldUdp64.

  Module Datetime.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime.

  Module MessageHeader.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime.encode_length. reflexivity.
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
      rewrite Datetime.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime.eq_dec]. Defined.

  End MessageHeader.

  Module TradeReportShortFormMessage.

    (** Economized trade report *)
    Record t := {
      message_header : MessageHeader.t;
      security_symbol_short : list byte;
      sale_condition_level_1 : list byte;
      trade_price_denominator : list byte;
      trade_price_short : list byte;
      report_volume_short : list byte;
      price_change_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record) /\
      Datatypes.length (security_symbol_short record) = 5 /\
      Datatypes.length (sale_condition_level_1 record) = 1 /\
      Datatypes.length (trade_price_denominator record) = 1 /\
      Datatypes.length (trade_price_short record) = 6 /\
      Datatypes.length (report_volume_short record) = 6 /\
      Datatypes.length (price_change_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record) ++
      encode_bytes 5 (security_symbol_short record) ++
      encode_bytes 1 (sale_condition_level_1 record) ++
      encode_bytes 1 (trade_price_denominator record) ++
      encode_bytes 6 (trade_price_short record) ++
      encode_bytes 6 (report_volume_short record) ++
      encode_bytes 1 (price_change_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (security_symbol_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sale_condition_level_1_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trade_price_denominator_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (trade_price_short_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (report_volume_short_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (price_change_indicator_value, bytes) =>
                                  Some ({| message_header := message_header_value; security_symbol_short := security_symbol_short_value; sale_condition_level_1 := sale_condition_level_1_value; trade_price_denominator := trade_price_denominator_value; trade_price_short := trade_price_short_value; report_volume_short := report_volume_short_value; price_change_indicator := price_change_indicator_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 53.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader.eq_dec]. Defined.

  End TradeReportShortFormMessage.

  Module Datetime2.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime2.

  Module MessageHeader2.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime2.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime2.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime2.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime2.encode_length. reflexivity.
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
      rewrite Datetime2.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime2.eq_dec]. Defined.

  End MessageHeader2.

  Module OriginalDisseminationDate.

    (** Original Dissemination Date *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  Some ({| year := year_value; month := month_value; day := day_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End OriginalDisseminationDate.

  Module ExecutionDatetime.

    (** Execution Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End ExecutionDatetime.

  Module TradeInformation.

    (** Trade Information *)
    Record t := {
      report_volume : list byte;
      trade_price_denominator : list byte;
      trade_price : list byte;
      currency : list byte;
      as_of_indicator : list byte;
      execution_datetime : ExecutionDatetime.t;
      sale_condition_level_1 : list byte;
      sale_condition_level_2 : list byte;
      sale_condition_level_3 : list byte;
      sale_condition_level_4 : list byte;
      sellers_sale_days : list byte;
      price_change_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (report_volume record) = 8 /\
      Datatypes.length (trade_price_denominator record) = 1 /\
      Datatypes.length (trade_price record) = 12 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (as_of_indicator record) = 1 /\
      ExecutionDatetime.bounded (execution_datetime record) /\
      Datatypes.length (sale_condition_level_1 record) = 1 /\
      Datatypes.length (sale_condition_level_2 record) = 1 /\
      Datatypes.length (sale_condition_level_3 record) = 1 /\
      Datatypes.length (sale_condition_level_4 record) = 1 /\
      Datatypes.length (sellers_sale_days record) = 2 /\
      Datatypes.length (price_change_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (report_volume record) ++
      encode_bytes 1 (trade_price_denominator record) ++
      encode_bytes 12 (trade_price record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (as_of_indicator record) ++
      ExecutionDatetime.encode (execution_datetime record) ++
      encode_bytes 1 (sale_condition_level_1 record) ++
      encode_bytes 1 (sale_condition_level_2 record) ++
      encode_bytes 1 (sale_condition_level_3 record) ++
      encode_bytes 1 (sale_condition_level_4 record) ++
      encode_bytes 2 (sellers_sale_days record) ++
      encode_bytes 1 (price_change_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (report_volume_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_denominator_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (trade_price_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (currency_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (as_of_indicator_value, bytes) =>
                          match ExecutionDatetime.decode bytes with
                          | None => None
                          | Some (execution_datetime_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (sale_condition_level_1_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sale_condition_level_2_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (sale_condition_level_3_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (sale_condition_level_4_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (price_change_indicator_value, bytes) =>
                                                      Some ({| report_volume := report_volume_value; trade_price_denominator := trade_price_denominator_value; trade_price := trade_price_value; currency := currency_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; sale_condition_level_1 := sale_condition_level_1_value; sale_condition_level_2 := sale_condition_level_2_value; sale_condition_level_3 := sale_condition_level_3_value; sale_condition_level_4 := sale_condition_level_4_value; sellers_sale_days := sellers_sale_days_value; price_change_indicator := price_change_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 55.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite ExecutionDatetime.decode_encode by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime.eq_dec]. Defined.

  End TradeInformation.

  Module TradeReportLongFormMessage.

    (** Complete trade report *)
    Record t := {
      message_header : MessageHeader2.t;
      security_symbol : list byte;
      original_dissemination_date : OriginalDisseminationDate.t;
      trade_information : TradeInformation.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader2.bounded (message_header record) /\
      Datatypes.length (security_symbol record) = 14 /\
      OriginalDisseminationDate.bounded (original_dissemination_date record) /\
      TradeInformation.bounded (trade_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader2.encode (message_header record) ++
      encode_bytes 14 (security_symbol record) ++
      OriginalDisseminationDate.encode (original_dissemination_date record) ++
      TradeInformation.encode (trade_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader2.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (security_symbol_value, bytes) =>
              match OriginalDisseminationDate.decode bytes with
              | None => None
              | Some (original_dissemination_date_value, bytes) =>
                  match TradeInformation.decode bytes with
                  | None => None
                  | Some (trade_information_value, bytes) =>
                      Some ({| message_header := message_header_value; security_symbol := security_symbol_value; original_dissemination_date := original_dissemination_date_value; trade_information := trade_information_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 110.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader2.encode_length, !encode_bytes_length, !OriginalDisseminationDate.encode_length, !TradeInformation.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader2.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite OriginalDisseminationDate.decode_encode by exact bound_2.
      rewrite TradeInformation.decode_encode by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader2.eq_dec | apply OriginalDisseminationDate.eq_dec | apply TradeInformation.eq_dec]. Defined.

  End TradeReportLongFormMessage.

  Module Datetime3.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime3.

  Module MessageHeader3.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime3.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime3.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime3.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime3.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime3.encode_length. reflexivity.
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
      rewrite Datetime3.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime3.eq_dec]. Defined.

  End MessageHeader3.

  Module OriginalDisseminationDate2.

    (** Original Dissemination Date *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  Some ({| year := year_value; month := month_value; day := day_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End OriginalDisseminationDate2.

  Module ExecutionDatetime2.

    (** Execution Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End ExecutionDatetime2.

  Module OriginalTradeInformation.

    (** Original Trade Information *)
    Record t := {
      report_volume : list byte;
      trade_price_denominator : list byte;
      trade_price : list byte;
      currency : list byte;
      as_of_indicator : list byte;
      execution_datetime : ExecutionDatetime2.t;
      sale_condition_level_1 : list byte;
      sale_condition_level_2 : list byte;
      sale_condition_level_3 : list byte;
      sale_condition_level_4 : list byte;
      sellers_sale_days : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (report_volume record) = 8 /\
      Datatypes.length (trade_price_denominator record) = 1 /\
      Datatypes.length (trade_price record) = 12 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (as_of_indicator record) = 1 /\
      ExecutionDatetime2.bounded (execution_datetime record) /\
      Datatypes.length (sale_condition_level_1 record) = 1 /\
      Datatypes.length (sale_condition_level_2 record) = 1 /\
      Datatypes.length (sale_condition_level_3 record) = 1 /\
      Datatypes.length (sale_condition_level_4 record) = 1 /\
      Datatypes.length (sellers_sale_days record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (report_volume record) ++
      encode_bytes 1 (trade_price_denominator record) ++
      encode_bytes 12 (trade_price record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (as_of_indicator record) ++
      ExecutionDatetime2.encode (execution_datetime record) ++
      encode_bytes 1 (sale_condition_level_1 record) ++
      encode_bytes 1 (sale_condition_level_2 record) ++
      encode_bytes 1 (sale_condition_level_3 record) ++
      encode_bytes 1 (sale_condition_level_4 record) ++
      encode_bytes 2 (sellers_sale_days record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (report_volume_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_denominator_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (trade_price_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (currency_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (as_of_indicator_value, bytes) =>
                          match ExecutionDatetime2.decode bytes with
                          | None => None
                          | Some (execution_datetime_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (sale_condition_level_1_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sale_condition_level_2_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (sale_condition_level_3_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (sale_condition_level_4_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  Some ({| report_volume := report_volume_value; trade_price_denominator := trade_price_denominator_value; trade_price := trade_price_value; currency := currency_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; sale_condition_level_1 := sale_condition_level_1_value; sale_condition_level_2 := sale_condition_level_2_value; sale_condition_level_3 := sale_condition_level_3_value; sale_condition_level_4 := sale_condition_level_4_value; sellers_sale_days := sellers_sale_days_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 54.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite ExecutionDatetime2.decode_encode by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime2.eq_dec]. Defined.

  End OriginalTradeInformation.

  Module TradeSummaryInformation.

    (** Trade Summary Information *)
    Record t := {
      high_price_denominator : list byte;
      high_price : list byte;
      low_price_denominator : list byte;
      low_price : list byte;
      last_sale_price_denominator : list byte;
      last_sale_price : list byte;
      last_sale_price_market_center : list byte;
      total_security_volume : list byte;
      price_change_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (high_price_denominator record) = 1 /\
      Datatypes.length (high_price record) = 12 /\
      Datatypes.length (low_price_denominator record) = 1 /\
      Datatypes.length (low_price record) = 12 /\
      Datatypes.length (last_sale_price_denominator record) = 1 /\
      Datatypes.length (last_sale_price record) = 12 /\
      Datatypes.length (last_sale_price_market_center record) = 1 /\
      Datatypes.length (total_security_volume record) = 11 /\
      Datatypes.length (price_change_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (high_price_denominator record) ++
      encode_bytes 12 (high_price record) ++
      encode_bytes 1 (low_price_denominator record) ++
      encode_bytes 12 (low_price record) ++
      encode_bytes 1 (last_sale_price_denominator record) ++
      encode_bytes 12 (last_sale_price record) ++
      encode_bytes 1 (last_sale_price_market_center record) ++
      encode_bytes 11 (total_security_volume record) ++
      encode_bytes 1 (price_change_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (high_price_denominator_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (high_price_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (low_price_denominator_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (low_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (last_sale_price_denominator_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (last_sale_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (last_sale_price_market_center_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (total_security_volume_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (price_change_indicator_value, bytes) =>
                                          Some ({| high_price_denominator := high_price_denominator_value; high_price := high_price_value; low_price_denominator := low_price_denominator_value; low_price := low_price_value; last_sale_price_denominator := last_sale_price_denominator_value; last_sale_price := last_sale_price_value; last_sale_price_market_center := last_sale_price_market_center_value; total_security_volume := total_security_volume_value; price_change_indicator := price_change_indicator_value |}, bytes)
                                      end
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeSummaryInformation.

  Module TradeCancelErrorMessage.

    (** This message is used to notify TDDS customers if a trade report entered during the current business day, or up to the past three business days, has been canceled *)
    Record t := {
      message_header : MessageHeader3.t;
      security_symbol : list byte;
      original_dissemination_date : OriginalDisseminationDate2.t;
      report_function : list byte;
      original_trade_information : OriginalTradeInformation.t;
      trade_summary_information : TradeSummaryInformation.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader3.bounded (message_header record) /\
      Datatypes.length (security_symbol record) = 14 /\
      OriginalDisseminationDate2.bounded (original_dissemination_date record) /\
      Datatypes.length (report_function record) = 1 /\
      OriginalTradeInformation.bounded (original_trade_information record) /\
      TradeSummaryInformation.bounded (trade_summary_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader3.encode (message_header record) ++
      encode_bytes 14 (security_symbol record) ++
      OriginalDisseminationDate2.encode (original_dissemination_date record) ++
      encode_bytes 1 (report_function record) ++
      OriginalTradeInformation.encode (original_trade_information record) ++
      TradeSummaryInformation.encode (trade_summary_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader3.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (security_symbol_value, bytes) =>
              match OriginalDisseminationDate2.decode bytes with
              | None => None
              | Some (original_dissemination_date_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (report_function_value, bytes) =>
                      match OriginalTradeInformation.decode bytes with
                      | None => None
                      | Some (original_trade_information_value, bytes) =>
                          match TradeSummaryInformation.decode bytes with
                          | None => None
                          | Some (trade_summary_information_value, bytes) =>
                              Some ({| message_header := message_header_value; security_symbol := security_symbol_value; original_dissemination_date := original_dissemination_date_value; report_function := report_function_value; original_trade_information := original_trade_information_value; trade_summary_information := trade_summary_information_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 162.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader3.encode_length, !encode_bytes_length, !OriginalDisseminationDate2.encode_length, !OriginalTradeInformation.encode_length, !TradeSummaryInformation.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader3.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite OriginalDisseminationDate2.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite OriginalTradeInformation.decode_encode by exact bound_4.
      rewrite TradeSummaryInformation.decode_encode by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader3.eq_dec | apply OriginalDisseminationDate2.eq_dec | apply OriginalTradeInformation.eq_dec | apply TradeSummaryInformation.eq_dec]. Defined.

  End TradeCancelErrorMessage.

  Module Datetime4.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime4.

  Module MessageHeader4.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime4.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime4.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime4.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime4.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime4.encode_length. reflexivity.
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
      rewrite Datetime4.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime4.eq_dec]. Defined.

  End MessageHeader4.

  Module OriginalDisseminationDate3.

    (** Original Dissemination Date *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  Some ({| year := year_value; month := month_value; day := day_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End OriginalDisseminationDate3.

  Module ExecutionDatetime3.

    (** Execution Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End ExecutionDatetime3.

  Module OriginalTradeInformation2.

    (** Original Trade Information *)
    Record t := {
      report_volume : list byte;
      trade_price_denominator : list byte;
      trade_price : list byte;
      currency : list byte;
      as_of_indicator : list byte;
      execution_datetime : ExecutionDatetime3.t;
      sale_condition_level_1 : list byte;
      sale_condition_level_2 : list byte;
      sale_condition_level_3 : list byte;
      sale_condition_level_4 : list byte;
      sellers_sale_days : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (report_volume record) = 8 /\
      Datatypes.length (trade_price_denominator record) = 1 /\
      Datatypes.length (trade_price record) = 12 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (as_of_indicator record) = 1 /\
      ExecutionDatetime3.bounded (execution_datetime record) /\
      Datatypes.length (sale_condition_level_1 record) = 1 /\
      Datatypes.length (sale_condition_level_2 record) = 1 /\
      Datatypes.length (sale_condition_level_3 record) = 1 /\
      Datatypes.length (sale_condition_level_4 record) = 1 /\
      Datatypes.length (sellers_sale_days record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (report_volume record) ++
      encode_bytes 1 (trade_price_denominator record) ++
      encode_bytes 12 (trade_price record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (as_of_indicator record) ++
      ExecutionDatetime3.encode (execution_datetime record) ++
      encode_bytes 1 (sale_condition_level_1 record) ++
      encode_bytes 1 (sale_condition_level_2 record) ++
      encode_bytes 1 (sale_condition_level_3 record) ++
      encode_bytes 1 (sale_condition_level_4 record) ++
      encode_bytes 2 (sellers_sale_days record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (report_volume_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_denominator_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (trade_price_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (currency_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (as_of_indicator_value, bytes) =>
                          match ExecutionDatetime3.decode bytes with
                          | None => None
                          | Some (execution_datetime_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (sale_condition_level_1_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sale_condition_level_2_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (sale_condition_level_3_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (sale_condition_level_4_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  Some ({| report_volume := report_volume_value; trade_price_denominator := trade_price_denominator_value; trade_price := trade_price_value; currency := currency_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; sale_condition_level_1 := sale_condition_level_1_value; sale_condition_level_2 := sale_condition_level_2_value; sale_condition_level_3 := sale_condition_level_3_value; sale_condition_level_4 := sale_condition_level_4_value; sellers_sale_days := sellers_sale_days_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 54.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite ExecutionDatetime3.decode_encode by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime3.eq_dec]. Defined.

  End OriginalTradeInformation2.

  Module ExecutionDatetime4.

    (** Execution Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End ExecutionDatetime4.

  Module CorrectedTradeInformation.

    (** Corrected Trade Information *)
    Record t := {
      report_volume : list byte;
      trade_price_denominator : list byte;
      trade_price : list byte;
      currency : list byte;
      as_of_indicator : list byte;
      execution_datetime : ExecutionDatetime4.t;
      sale_condition_level_1 : list byte;
      sale_condition_level_2 : list byte;
      sale_condition_level_3 : list byte;
      sale_condition_level_4 : list byte;
      sellers_sale_days : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (report_volume record) = 8 /\
      Datatypes.length (trade_price_denominator record) = 1 /\
      Datatypes.length (trade_price record) = 12 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (as_of_indicator record) = 1 /\
      ExecutionDatetime4.bounded (execution_datetime record) /\
      Datatypes.length (sale_condition_level_1 record) = 1 /\
      Datatypes.length (sale_condition_level_2 record) = 1 /\
      Datatypes.length (sale_condition_level_3 record) = 1 /\
      Datatypes.length (sale_condition_level_4 record) = 1 /\
      Datatypes.length (sellers_sale_days record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (report_volume record) ++
      encode_bytes 1 (trade_price_denominator record) ++
      encode_bytes 12 (trade_price record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (as_of_indicator record) ++
      ExecutionDatetime4.encode (execution_datetime record) ++
      encode_bytes 1 (sale_condition_level_1 record) ++
      encode_bytes 1 (sale_condition_level_2 record) ++
      encode_bytes 1 (sale_condition_level_3 record) ++
      encode_bytes 1 (sale_condition_level_4 record) ++
      encode_bytes 2 (sellers_sale_days record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (report_volume_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_denominator_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (trade_price_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (currency_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (as_of_indicator_value, bytes) =>
                          match ExecutionDatetime4.decode bytes with
                          | None => None
                          | Some (execution_datetime_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (sale_condition_level_1_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sale_condition_level_2_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (sale_condition_level_3_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (sale_condition_level_4_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  Some ({| report_volume := report_volume_value; trade_price_denominator := trade_price_denominator_value; trade_price := trade_price_value; currency := currency_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; sale_condition_level_1 := sale_condition_level_1_value; sale_condition_level_2 := sale_condition_level_2_value; sale_condition_level_3 := sale_condition_level_3_value; sale_condition_level_4 := sale_condition_level_4_value; sellers_sale_days := sellers_sale_days_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 54.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime4.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite ExecutionDatetime4.decode_encode by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime4.eq_dec]. Defined.

  End CorrectedTradeInformation.

  Module TradeSummaryInformation2.

    (** Trade Summary Information *)
    Record t := {
      high_price_denominator : list byte;
      high_price : list byte;
      low_price_denominator : list byte;
      low_price : list byte;
      last_sale_price_denominator : list byte;
      last_sale_price : list byte;
      last_sale_price_market_center : list byte;
      total_security_volume : list byte;
      price_change_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (high_price_denominator record) = 1 /\
      Datatypes.length (high_price record) = 12 /\
      Datatypes.length (low_price_denominator record) = 1 /\
      Datatypes.length (low_price record) = 12 /\
      Datatypes.length (last_sale_price_denominator record) = 1 /\
      Datatypes.length (last_sale_price record) = 12 /\
      Datatypes.length (last_sale_price_market_center record) = 1 /\
      Datatypes.length (total_security_volume record) = 11 /\
      Datatypes.length (price_change_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (high_price_denominator record) ++
      encode_bytes 12 (high_price record) ++
      encode_bytes 1 (low_price_denominator record) ++
      encode_bytes 12 (low_price record) ++
      encode_bytes 1 (last_sale_price_denominator record) ++
      encode_bytes 12 (last_sale_price record) ++
      encode_bytes 1 (last_sale_price_market_center record) ++
      encode_bytes 11 (total_security_volume record) ++
      encode_bytes 1 (price_change_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (high_price_denominator_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (high_price_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (low_price_denominator_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (low_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (last_sale_price_denominator_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (last_sale_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (last_sale_price_market_center_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (total_security_volume_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (price_change_indicator_value, bytes) =>
                                          Some ({| high_price_denominator := high_price_denominator_value; high_price := high_price_value; low_price_denominator := low_price_denominator_value; low_price := low_price_value; last_sale_price_denominator := last_sale_price_denominator_value; last_sale_price := last_sale_price_value; last_sale_price_market_center := last_sale_price_market_center_value; total_security_volume := total_security_volume_value; price_change_indicator := price_change_indicator_value |}, bytes)
                                      end
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeSummaryInformation2.

  Module TradeCorrectionMessage.

    (** Used to notify TDDS customers if a trade report entered during the current business day, or up to the past three business days, has been modified *)
    Record t := {
      message_header : MessageHeader4.t;
      security_symbol : list byte;
      original_dissemination_date : OriginalDisseminationDate3.t;
      report_function : list byte;
      original_trade_information : OriginalTradeInformation2.t;
      corrected_trade_information : CorrectedTradeInformation.t;
      trade_summary_information : TradeSummaryInformation2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader4.bounded (message_header record) /\
      Datatypes.length (security_symbol record) = 14 /\
      OriginalDisseminationDate3.bounded (original_dissemination_date record) /\
      Datatypes.length (report_function record) = 1 /\
      OriginalTradeInformation2.bounded (original_trade_information record) /\
      CorrectedTradeInformation.bounded (corrected_trade_information record) /\
      TradeSummaryInformation2.bounded (trade_summary_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader4.encode (message_header record) ++
      encode_bytes 14 (security_symbol record) ++
      OriginalDisseminationDate3.encode (original_dissemination_date record) ++
      encode_bytes 1 (report_function record) ++
      OriginalTradeInformation2.encode (original_trade_information record) ++
      CorrectedTradeInformation.encode (corrected_trade_information record) ++
      TradeSummaryInformation2.encode (trade_summary_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader4.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (security_symbol_value, bytes) =>
              match OriginalDisseminationDate3.decode bytes with
              | None => None
              | Some (original_dissemination_date_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (report_function_value, bytes) =>
                      match OriginalTradeInformation2.decode bytes with
                      | None => None
                      | Some (original_trade_information_value, bytes) =>
                          match CorrectedTradeInformation.decode bytes with
                          | None => None
                          | Some (corrected_trade_information_value, bytes) =>
                              match TradeSummaryInformation2.decode bytes with
                              | None => None
                              | Some (trade_summary_information_value, bytes) =>
                                  Some ({| message_header := message_header_value; security_symbol := security_symbol_value; original_dissemination_date := original_dissemination_date_value; report_function := report_function_value; original_trade_information := original_trade_information_value; corrected_trade_information := corrected_trade_information_value; trade_summary_information := trade_summary_information_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 216.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader4.encode_length, !encode_bytes_length, !OriginalDisseminationDate3.encode_length, !OriginalTradeInformation2.encode_length, !CorrectedTradeInformation.encode_length, !TradeSummaryInformation2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader4.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite OriginalDisseminationDate3.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite OriginalTradeInformation2.decode_encode by exact bound_4.
      rewrite CorrectedTradeInformation.decode_encode by exact bound_5.
      rewrite TradeSummaryInformation2.decode_encode by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader4.eq_dec | apply OriginalDisseminationDate3.eq_dec | apply OriginalTradeInformation2.eq_dec | apply CorrectedTradeInformation.eq_dec | apply TradeSummaryInformation2.eq_dec]. Defined.

  End TradeCorrectionMessage.

  Module Datetime5.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime5.

  Module MessageHeader5.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime5.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime5.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime5.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime5.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime5.encode_length. reflexivity.
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
      rewrite Datetime5.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime5.eq_dec]. Defined.

  End MessageHeader5.

  Module Datetime6.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime6.

  Module MessageHeader6.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime6.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime6.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime6.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime6.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime6.encode_length. reflexivity.
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
      rewrite Datetime6.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime6.eq_dec]. Defined.

  End MessageHeader6.

  Module ClosingTradeSummaryReportMessage.

    (** The closing trade summary will reflect the daily high, low, and closing prices as well as the total volume for the security *)
    Record t := {
      message_header : MessageHeader6.t;
      security_symbol : list byte;
      daily_high_price_denominator : list byte;
      daily_high_price : list byte;
      daily_low_price_denominator : list byte;
      daily_low_price : list byte;
      closing_price_market_center : list byte;
      closing_price_denominator : list byte;
      closing_price : list byte;
      reserved_1 : list byte;
      net_change_denominator : list byte;
      net_change_amount : list byte;
      net_change_direction : list byte;
      currency : list byte;
      total_security_volume : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader6.bounded (message_header record) /\
      Datatypes.length (security_symbol record) = 14 /\
      Datatypes.length (daily_high_price_denominator record) = 1 /\
      Datatypes.length (daily_high_price record) = 12 /\
      Datatypes.length (daily_low_price_denominator record) = 1 /\
      Datatypes.length (daily_low_price record) = 12 /\
      Datatypes.length (closing_price_market_center record) = 1 /\
      Datatypes.length (closing_price_denominator record) = 1 /\
      Datatypes.length (closing_price record) = 12 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (net_change_denominator record) = 1 /\
      Datatypes.length (net_change_amount record) = 10 /\
      Datatypes.length (net_change_direction record) = 1 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (total_security_volume record) = 11.

    Definition encode (record : t) : list byte :=
      MessageHeader6.encode (message_header record) ++
      encode_bytes 14 (security_symbol record) ++
      encode_bytes 1 (daily_high_price_denominator record) ++
      encode_bytes 12 (daily_high_price record) ++
      encode_bytes 1 (daily_low_price_denominator record) ++
      encode_bytes 12 (daily_low_price record) ++
      encode_bytes 1 (closing_price_market_center record) ++
      encode_bytes 1 (closing_price_denominator record) ++
      encode_bytes 12 (closing_price record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (net_change_denominator record) ++
      encode_bytes 10 (net_change_amount record) ++
      encode_bytes 1 (net_change_direction record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 11 (total_security_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader6.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (security_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (daily_high_price_denominator_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (daily_high_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (daily_low_price_denominator_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (daily_low_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (closing_price_market_center_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (closing_price_denominator_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (closing_price_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (reserved_1_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (net_change_denominator_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (net_change_amount_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (net_change_direction_value, bytes) =>
                                                          match decode_bytes 3 bytes with
                                                          | None => None
                                                          | Some (currency_value, bytes) =>
                                                              match decode_bytes 11 bytes with
                                                              | None => None
                                                              | Some (total_security_volume_value, bytes) =>
                                                                  Some ({| message_header := message_header_value; security_symbol := security_symbol_value; daily_high_price_denominator := daily_high_price_denominator_value; daily_high_price := daily_high_price_value; daily_low_price_denominator := daily_low_price_denominator_value; daily_low_price := daily_low_price_value; closing_price_market_center := closing_price_market_center_value; closing_price_denominator := closing_price_denominator_value; closing_price := closing_price_value; reserved_1 := reserved_1_value; net_change_denominator := net_change_denominator_value; net_change_amount := net_change_amount_value; net_change_direction := net_change_direction_value; currency := currency_value; total_security_volume := total_security_volume_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 114.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader6.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader6.decode_encode by exact bound_0.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader6.eq_dec]. Defined.

  End ClosingTradeSummaryReportMessage.

  Module Datetime7.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime7.

  Module MessageHeader7.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime7.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime7.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime7.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime7.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime7.encode_length. reflexivity.
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
      rewrite Datetime7.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime7.eq_dec]. Defined.

  End MessageHeader7.

  Module ActionDatetime.

    (** Action Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End ActionDatetime.

  Module TradingActionMessage.

    (** FINRA will disseminate this message to inform customers of trading actions, such as halts or trading resumptions which affect individual OTCBB or Other OTC securities *)
    Record t := {
      message_header : MessageHeader7.t;
      security_symbol : list byte;
      action : list byte;
      action_datetime : ActionDatetime.t;
      trading_action_reason_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader7.bounded (message_header record) /\
      Datatypes.length (security_symbol record) = 14 /\
      Datatypes.length (action record) = 1 /\
      ActionDatetime.bounded (action_datetime record) /\
      Datatypes.length (trading_action_reason_code record) = 6.

    Definition encode (record : t) : list byte :=
      MessageHeader7.encode (message_header record) ++
      encode_bytes 14 (security_symbol record) ++
      encode_bytes 1 (action record) ++
      ActionDatetime.encode (action_datetime record) ++
      encode_bytes 6 (trading_action_reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader7.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (security_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (action_value, bytes) =>
                  match ActionDatetime.decode bytes with
                  | None => None
                  | Some (action_datetime_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (trading_action_reason_code_value, bytes) =>
                          Some ({| message_header := message_header_value; security_symbol := security_symbol_value; action := action_value; action_datetime := action_datetime_value; trading_action_reason_code := trading_action_reason_code_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 77.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader7.encode_length, !encode_bytes_length, !ActionDatetime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader7.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite ActionDatetime.decode_encode by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader7.eq_dec | apply ActionDatetime.eq_dec]. Defined.

  End TradingActionMessage.

  Module Datetime8.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime8.

  Module MessageHeader8.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime8.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime8.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime8.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime8.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime8.encode_length. reflexivity.
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
      rewrite Datetime8.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime8.eq_dec]. Defined.

  End MessageHeader8.

  Module ActionDatetime2.

    (** Action Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End ActionDatetime2.

  Module MarketWideCircuitBreakerEventMessage.

    (** FINRA will disseminate this message to inform customers of an extraordinary market event trading action or a market wide circuit breaker event which will affect all security symbols for either OTCBB, Other OTC or both OTCBB and Other OTC market places *)
    Record t := {
      message_header : MessageHeader8.t;
      action : list byte;
      action_datetime : ActionDatetime2.t;
      market_wide_circuit_breaker_reason_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader8.bounded (message_header record) /\
      Datatypes.length (action record) = 1 /\
      ActionDatetime2.bounded (action_datetime record) /\
      Datatypes.length (market_wide_circuit_breaker_reason_code record) = 6.

    Definition encode (record : t) : list byte :=
      MessageHeader8.encode (message_header record) ++
      encode_bytes 1 (action record) ++
      ActionDatetime2.encode (action_datetime record) ++
      encode_bytes 6 (market_wide_circuit_breaker_reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader8.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (action_value, bytes) =>
              match ActionDatetime2.decode bytes with
              | None => None
              | Some (action_datetime_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (market_wide_circuit_breaker_reason_code_value, bytes) =>
                      Some ({| message_header := message_header_value; action := action_value; action_datetime := action_datetime_value; market_wide_circuit_breaker_reason_code := market_wide_circuit_breaker_reason_code_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader8.encode_length, !encode_bytes_length, !ActionDatetime2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader8.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite ActionDatetime2.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader8.eq_dec | apply ActionDatetime2.eq_dec]. Defined.

  End MarketWideCircuitBreakerEventMessage.

  Module Datetime9.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime9.

  Module MessageHeader9.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime9.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime9.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime9.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime9.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime9.encode_length. reflexivity.
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
      rewrite Datetime9.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime9.eq_dec]. Defined.

  End MessageHeader9.

  Module StartOfDayMessage.

    (** The Start of Day control message signifies the beginning of each operational cycle for TDDS processing *)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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

  End StartOfDayMessage.

  Module Datetime10.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime10.

  Module MessageHeader10.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime10.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime10.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime10.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime10.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime10.encode_length. reflexivity.
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
      rewrite Datetime10.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime10.eq_dec]. Defined.

  End MessageHeader10.

  Module EndOfDayMessage.

    (** The End of Day control message signals the end of active message dissemination for the TDDS operational cycle *)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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

  End EndOfDayMessage.

  Module Datetime11.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime11.

  Module MessageHeader11.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime11.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime11.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime11.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime11.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime11.encode_length. reflexivity.
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
      rewrite Datetime11.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime11.eq_dec]. Defined.

  End MessageHeader11.

  Module MarketSessionOpenMessage.

    (** The Market Session Open Control Message signifies the opening of FINRA’s market systems for the session indicated in the Message Header *)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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

  End MarketSessionOpenMessage.

  Module Datetime12.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime12.

  Module MessageHeader12.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime12.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime12.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime12.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime12.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime12.encode_length. reflexivity.
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
      rewrite Datetime12.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime12.eq_dec]. Defined.

  End MessageHeader12.

  Module MarketSessionCloseMessage.

    (** The Session Close Control Message signals the closing of FINRA’s market systems for the session indicated in the Message Header *)
    Record t := {
      message_header : MessageHeader12.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader12.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader12.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader12.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader12.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader12.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader12.eq_dec]. Defined.

  End MarketSessionCloseMessage.

  Module Datetime13.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime13.

  Module MessageHeader13.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime13.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime13.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime13.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime13.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime13.encode_length. reflexivity.
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
      rewrite Datetime13.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime13.eq_dec]. Defined.

  End MessageHeader13.

  Module EndOfRetransmissionRequestsMessage.

    (** This message signals that no further retransmission requests will be honored. The End of Retransmission Requests message will be sent three times, at one-minute intervals *)
    Record t := {
      message_header : MessageHeader13.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader13.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader13.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader13.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader13.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader13.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader13.eq_dec]. Defined.

  End EndOfRetransmissionRequestsMessage.

  Module Datetime14.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime14.

  Module MessageHeader14.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime14.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime14.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime14.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime14.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime14.encode_length. reflexivity.
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
      rewrite Datetime14.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime14.eq_dec]. Defined.

  End MessageHeader14.

  Module EndOfTransmissionsMessage.

    (** The End of Transmissions Message signals that there will be no further transmissions of data sent through the TDDS line. *)
    Record t := {
      message_header : MessageHeader14.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader14.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader14.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader14.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader14.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader14.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader14.eq_dec]. Defined.

  End EndOfTransmissionsMessage.

  Module Datetime15.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime15.

  Module MessageHeader15.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime15.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime15.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime15.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime15.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime15.encode_length. reflexivity.
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
      rewrite Datetime15.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime15.eq_dec]. Defined.

  End MessageHeader15.

  Module LineIntegrityMessage.

    (** The Line Integrity Control Message will be transmitted at approximately one-minute intervals to verify the operational integrity of the TDDS message transmission, and will be intermixed with other messages *)
    Record t := {
      message_header : MessageHeader15.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader15.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader15.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader15.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader15.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader15.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader15.eq_dec]. Defined.

  End LineIntegrityMessage.

  Module Datetime16.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime16.

  Module MessageHeader16.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime16.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime16.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime16.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime16.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime16.encode_length. reflexivity.
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
      rewrite Datetime16.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime16.eq_dec]. Defined.

  End MessageHeader16.

  Module SequenceNumberResetMessage.

    (** The Sequence Number Reset Message forces the resetting of the Sequence Number. The Sequence Number will either be reset to zero or to a number greater than the last number previously transmitted *)
    Record t := {
      message_header : MessageHeader16.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader16.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader16.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader16.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader16.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader16.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader16.eq_dec]. Defined.

  End SequenceNumberResetMessage.

  Module Datetime17.

    (** Datetime *)
    Record t := {
      year : list byte;
      month : list byte;
      day : list byte;
      hour : list byte;
      minute : list byte;
      second : list byte;
      fractional_second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2 /\
      Datatypes.length (fractional_second record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record) ++
      encode_bytes 9 (fractional_second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (hour_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (minute_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (second_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (fractional_second_value, bytes) =>
                                  Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value; fractional_second := fractional_second_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End Datetime17.

  Module MessageHeader17.

    (** Message Header *)
    Record t := {
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime17.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 8 /\
      Datatypes.length (market_center_originator_id record) = 2 /\
      Datetime17.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trade_identifier record) ++
      encode_bytes 2 (market_center_originator_id record) ++
      Datetime17.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime17.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Datetime17.encode_length. reflexivity.
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
      rewrite Datetime17.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Datetime17.eq_dec]. Defined.

  End MessageHeader17.

  Module EndOfTradeReportingMessage.

    (** The End of Trade Reporting Control Message signals that the ORF system is closed for market participant trade transactions *)
    Record t := {
      message_header : MessageHeader17.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader17.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader17.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader17.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader17.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader17.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader17.eq_dec]. Defined.

  End EndOfTradeReportingMessage.

End FinraOrfTddsV21.
