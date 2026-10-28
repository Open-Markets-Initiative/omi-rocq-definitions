From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Financial Industry Regulatory Authority Agency Debt Trade Dissemination Service

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

Module TraceAtdsV21.

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
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module Label.

    (** Label *)
    Record t := {
      symbol : list byte;
      cusip : list byte;
      bsym : list byte;
      sub_product_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 14 /\
      Datatypes.length (cusip record) = 9 /\
      Datatypes.length (bsym record) = 12 /\
      Datatypes.length (sub_product_type record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (symbol record) ++
      encode_bytes 9 (cusip record) ++
      encode_bytes 12 (bsym record) ++
      encode_bytes 5 (sub_product_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (cusip_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (bsym_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (sub_product_type_value, bytes) =>
                      Some ({| symbol := symbol_value; cusip := cusip_value; bsym := bsym_value; sub_product_type := sub_product_type_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End Label.

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
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End ExecutionDatetime.

  Module SettlementDate.

    (** Settlement Date *)
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

  End SettlementDate.

  Module TradeInformation.

    (** Trade Information *)
    Record t := {
      quantity_indicator : list byte;
      quantity : list byte;
      price : list byte;
      remuneration : list byte;
      special_price_indicator : list byte;
      side : list byte;
      as_of_indicator : list byte;
      execution_datetime : ExecutionDatetime.t;
      future_use : list byte;
      sale_condition_3 : list byte;
      sale_condition_4 : list byte;
      settlement_date : SettlementDate.t;
      yield_direction : list byte;
      yield : list byte;
      when_issued_indicator : list byte;
      reporting_party_type : list byte;
      contra_party_type : list byte;
      ats_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (quantity_indicator record) = 1 /\
      Datatypes.length (quantity record) = 14 /\
      Datatypes.length (price record) = 11 /\
      Datatypes.length (remuneration record) = 1 /\
      Datatypes.length (special_price_indicator record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (as_of_indicator record) = 1 /\
      ExecutionDatetime.bounded (execution_datetime record) /\
      Datatypes.length (future_use record) = 2 /\
      Datatypes.length (sale_condition_3 record) = 1 /\
      Datatypes.length (sale_condition_4 record) = 1 /\
      SettlementDate.bounded (settlement_date record) /\
      Datatypes.length (yield_direction record) = 1 /\
      Datatypes.length (yield record) = 13 /\
      Datatypes.length (when_issued_indicator record) = 1 /\
      Datatypes.length (reporting_party_type record) = 1 /\
      Datatypes.length (contra_party_type record) = 1 /\
      Datatypes.length (ats_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (quantity_indicator record) ++
      encode_bytes 14 (quantity record) ++
      encode_bytes 11 (price record) ++
      encode_bytes 1 (remuneration record) ++
      encode_bytes 1 (special_price_indicator record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (as_of_indicator record) ++
      ExecutionDatetime.encode (execution_datetime record) ++
      encode_bytes 2 (future_use record) ++
      encode_bytes 1 (sale_condition_3 record) ++
      encode_bytes 1 (sale_condition_4 record) ++
      SettlementDate.encode (settlement_date record) ++
      encode_bytes 1 (yield_direction record) ++
      encode_bytes 13 (yield record) ++
      encode_bytes 1 (when_issued_indicator record) ++
      encode_bytes 1 (reporting_party_type record) ++
      encode_bytes 1 (contra_party_type record) ++
      encode_bytes 1 (ats_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (quantity_indicator_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (quantity_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (remuneration_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (special_price_indicator_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (as_of_indicator_value, bytes) =>
                                  match ExecutionDatetime.decode bytes with
                                  | None => None
                                  | Some (execution_datetime_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (future_use_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (sale_condition_3_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (sale_condition_4_value, bytes) =>
                                                  match SettlementDate.decode bytes with
                                                  | None => None
                                                  | Some (settlement_date_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (yield_direction_value, bytes) =>
                                                          match decode_bytes 13 bytes with
                                                          | None => None
                                                          | Some (yield_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (when_issued_indicator_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (reporting_party_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (contra_party_type_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (ats_indicator_value, bytes) =>
                                                                              Some ({| quantity_indicator := quantity_indicator_value; quantity := quantity_value; price := price_value; remuneration := remuneration_value; special_price_indicator := special_price_indicator_value; side := side_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; future_use := future_use_value; sale_condition_3 := sale_condition_3_value; sale_condition_4 := sale_condition_4_value; settlement_date := settlement_date_value; yield_direction := yield_direction_value; yield := yield_value; when_issued_indicator := when_issued_indicator_value; reporting_party_type := reporting_party_type_value; contra_party_type := contra_party_type_value; ats_indicator := ats_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime.encode_length, !SettlementDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite ExecutionDatetime.decode_encode by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite SettlementDate.decode_encode by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime.eq_dec | apply SettlementDate.eq_dec]. Defined.

  End TradeInformation.

  Module TradeReportMessage.

    (** Used to transmit agency debt trade transaction information to subscribers *)
    Record t := {
      message_header : MessageHeader.t;
      label : Label.t;
      original_dissemination_date : OriginalDisseminationDate.t;
      trade_information : TradeInformation.t;
      change_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record) /\
      Label.bounded (label record) /\
      OriginalDisseminationDate.bounded (original_dissemination_date record) /\
      TradeInformation.bounded (trade_information record) /\
      Datatypes.length (change_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record) ++
      Label.encode (label record) ++
      OriginalDisseminationDate.encode (original_dissemination_date record) ++
      TradeInformation.encode (trade_information record) ++
      encode_bytes 1 (change_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match Label.decode bytes with
          | None => None
          | Some (label_value, bytes) =>
              match OriginalDisseminationDate.decode bytes with
              | None => None
              | Some (original_dissemination_date_value, bytes) =>
                  match TradeInformation.decode bytes with
                  | None => None
                  | Some (trade_information_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (change_indicator_value, bytes) =>
                          Some ({| message_header := message_header_value; label := label_value; original_dissemination_date := original_dissemination_date_value; trade_information := trade_information_value; change_indicator := change_indicator_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 145.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader.encode_length, !Label.encode_length, !OriginalDisseminationDate.encode_length, !TradeInformation.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader.decode_encode by exact bound_0.
      rewrite Label.decode_encode by exact bound_1.
      rewrite OriginalDisseminationDate.decode_encode by exact bound_2.
      rewrite TradeInformation.decode_encode by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader.eq_dec | apply Label.eq_dec | apply OriginalDisseminationDate.eq_dec | apply TradeInformation.eq_dec]. Defined.

  End TradeReportMessage.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime2.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime2.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime2.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module Label2.

    (** Label *)
    Record t := {
      symbol : list byte;
      cusip : list byte;
      bsym : list byte;
      sub_product_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 14 /\
      Datatypes.length (cusip record) = 9 /\
      Datatypes.length (bsym record) = 12 /\
      Datatypes.length (sub_product_type record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (symbol record) ++
      encode_bytes 9 (cusip record) ++
      encode_bytes 12 (bsym record) ++
      encode_bytes 5 (sub_product_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (cusip_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (bsym_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (sub_product_type_value, bytes) =>
                      Some ({| symbol := symbol_value; cusip := cusip_value; bsym := bsym_value; sub_product_type := sub_product_type_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End Label2.

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
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End ExecutionDatetime2.

  Module SettlementDate2.

    (** Settlement Date *)
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

  End SettlementDate2.

  Module OriginalTradeInformation.

    (** Original Trade Information *)
    Record t := {
      quantity_indicator : list byte;
      quantity : list byte;
      price : list byte;
      remuneration : list byte;
      special_price_indicator : list byte;
      side : list byte;
      as_of_indicator : list byte;
      execution_datetime : ExecutionDatetime2.t;
      future_use : list byte;
      sale_condition_3 : list byte;
      sale_condition_4 : list byte;
      settlement_date : SettlementDate2.t;
      yield_direction : list byte;
      yield : list byte;
      when_issued_indicator : list byte;
      reporting_party_type : list byte;
      contra_party_type : list byte;
      ats_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (quantity_indicator record) = 1 /\
      Datatypes.length (quantity record) = 14 /\
      Datatypes.length (price record) = 11 /\
      Datatypes.length (remuneration record) = 1 /\
      Datatypes.length (special_price_indicator record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (as_of_indicator record) = 1 /\
      ExecutionDatetime2.bounded (execution_datetime record) /\
      Datatypes.length (future_use record) = 2 /\
      Datatypes.length (sale_condition_3 record) = 1 /\
      Datatypes.length (sale_condition_4 record) = 1 /\
      SettlementDate2.bounded (settlement_date record) /\
      Datatypes.length (yield_direction record) = 1 /\
      Datatypes.length (yield record) = 13 /\
      Datatypes.length (when_issued_indicator record) = 1 /\
      Datatypes.length (reporting_party_type record) = 1 /\
      Datatypes.length (contra_party_type record) = 1 /\
      Datatypes.length (ats_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (quantity_indicator record) ++
      encode_bytes 14 (quantity record) ++
      encode_bytes 11 (price record) ++
      encode_bytes 1 (remuneration record) ++
      encode_bytes 1 (special_price_indicator record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (as_of_indicator record) ++
      ExecutionDatetime2.encode (execution_datetime record) ++
      encode_bytes 2 (future_use record) ++
      encode_bytes 1 (sale_condition_3 record) ++
      encode_bytes 1 (sale_condition_4 record) ++
      SettlementDate2.encode (settlement_date record) ++
      encode_bytes 1 (yield_direction record) ++
      encode_bytes 13 (yield record) ++
      encode_bytes 1 (when_issued_indicator record) ++
      encode_bytes 1 (reporting_party_type record) ++
      encode_bytes 1 (contra_party_type record) ++
      encode_bytes 1 (ats_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (quantity_indicator_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (quantity_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (remuneration_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (special_price_indicator_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (as_of_indicator_value, bytes) =>
                                  match ExecutionDatetime2.decode bytes with
                                  | None => None
                                  | Some (execution_datetime_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (future_use_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (sale_condition_3_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (sale_condition_4_value, bytes) =>
                                                  match SettlementDate2.decode bytes with
                                                  | None => None
                                                  | Some (settlement_date_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (yield_direction_value, bytes) =>
                                                          match decode_bytes 13 bytes with
                                                          | None => None
                                                          | Some (yield_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (when_issued_indicator_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (reporting_party_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (contra_party_type_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (ats_indicator_value, bytes) =>
                                                                              Some ({| quantity_indicator := quantity_indicator_value; quantity := quantity_value; price := price_value; remuneration := remuneration_value; special_price_indicator := special_price_indicator_value; side := side_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; future_use := future_use_value; sale_condition_3 := sale_condition_3_value; sale_condition_4 := sale_condition_4_value; settlement_date := settlement_date_value; yield_direction := yield_direction_value; yield := yield_value; when_issued_indicator := when_issued_indicator_value; reporting_party_type := reporting_party_type_value; contra_party_type := contra_party_type_value; ats_indicator := ats_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime2.encode_length, !SettlementDate2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite ExecutionDatetime2.decode_encode by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite SettlementDate2.decode_encode by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime2.eq_dec | apply SettlementDate2.eq_dec]. Defined.

  End OriginalTradeInformation.

  Module TradeSummaryInformation.

    (** Trade Summary Information *)
    Record t := {
      high_price : list byte;
      high_yield_direction : list byte;
      high_yield : list byte;
      low_price : list byte;
      low_yield_direction : list byte;
      low_yield : list byte;
      last_sale_price : list byte;
      last_sale_yield_direction : list byte;
      last_sale_yield : list byte;
      change_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (high_price record) = 11 /\
      Datatypes.length (high_yield_direction record) = 1 /\
      Datatypes.length (high_yield record) = 13 /\
      Datatypes.length (low_price record) = 11 /\
      Datatypes.length (low_yield_direction record) = 1 /\
      Datatypes.length (low_yield record) = 13 /\
      Datatypes.length (last_sale_price record) = 11 /\
      Datatypes.length (last_sale_yield_direction record) = 1 /\
      Datatypes.length (last_sale_yield record) = 13 /\
      Datatypes.length (change_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (high_price record) ++
      encode_bytes 1 (high_yield_direction record) ++
      encode_bytes 13 (high_yield record) ++
      encode_bytes 11 (low_price record) ++
      encode_bytes 1 (low_yield_direction record) ++
      encode_bytes 13 (low_yield record) ++
      encode_bytes 11 (last_sale_price record) ++
      encode_bytes 1 (last_sale_yield_direction record) ++
      encode_bytes 13 (last_sale_yield record) ++
      encode_bytes 1 (change_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_yield_direction_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (high_yield_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (low_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (low_yield_direction_value, bytes) =>
                          match decode_bytes 13 bytes with
                          | None => None
                          | Some (low_yield_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (last_sale_price_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (last_sale_yield_direction_value, bytes) =>
                                      match decode_bytes 13 bytes with
                                      | None => None
                                      | Some (last_sale_yield_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (change_indicator_value, bytes) =>
                                              Some ({| high_price := high_price_value; high_yield_direction := high_yield_direction_value; high_yield := high_yield_value; low_price := low_price_value; low_yield_direction := low_yield_direction_value; low_yield := low_yield_value; last_sale_price := last_sale_price_value; last_sale_yield_direction := last_sale_yield_direction_value; last_sale_yield := last_sale_yield_value; change_indicator := change_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeSummaryInformation.

  Module TradeCancelMessage.

    (** Used to notify subscribers that a trade report entered during the current business day, or up to the past 19 business days, has been cancelled *)
    Record t := {
      message_header : MessageHeader2.t;
      label : Label2.t;
      original_dissemination_date : OriginalDisseminationDate2.t;
      original_trade_identifier : list byte;
      report_function : list byte;
      original_trade_information : OriginalTradeInformation.t;
      trade_summary_information : TradeSummaryInformation.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader2.bounded (message_header record) /\
      Label2.bounded (label record) /\
      OriginalDisseminationDate2.bounded (original_dissemination_date record) /\
      Datatypes.length (original_trade_identifier record) = 7 /\
      Datatypes.length (report_function record) = 1 /\
      OriginalTradeInformation.bounded (original_trade_information record) /\
      TradeSummaryInformation.bounded (trade_summary_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader2.encode (message_header record) ++
      Label2.encode (label record) ++
      OriginalDisseminationDate2.encode (original_dissemination_date record) ++
      encode_bytes 7 (original_trade_identifier record) ++
      encode_bytes 1 (report_function record) ++
      OriginalTradeInformation.encode (original_trade_information record) ++
      TradeSummaryInformation.encode (trade_summary_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader2.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match Label2.decode bytes with
          | None => None
          | Some (label_value, bytes) =>
              match OriginalDisseminationDate2.decode bytes with
              | None => None
              | Some (original_dissemination_date_value, bytes) =>
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (original_trade_identifier_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (report_function_value, bytes) =>
                          match OriginalTradeInformation.decode bytes with
                          | None => None
                          | Some (original_trade_information_value, bytes) =>
                              match TradeSummaryInformation.decode bytes with
                              | None => None
                              | Some (trade_summary_information_value, bytes) =>
                                  Some ({| message_header := message_header_value; label := label_value; original_dissemination_date := original_dissemination_date_value; original_trade_identifier := original_trade_identifier_value; report_function := report_function_value; original_trade_information := original_trade_information_value; trade_summary_information := trade_summary_information_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 228.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader2.encode_length, !Label2.encode_length, !OriginalDisseminationDate2.encode_length, !encode_bytes_length, !OriginalTradeInformation.encode_length, !TradeSummaryInformation.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader2.decode_encode by exact bound_0.
      rewrite Label2.decode_encode by exact bound_1.
      rewrite OriginalDisseminationDate2.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite OriginalTradeInformation.decode_encode by exact bound_5.
      rewrite TradeSummaryInformation.decode_encode by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader2.eq_dec | apply Label2.eq_dec | apply OriginalDisseminationDate2.eq_dec | apply OriginalTradeInformation.eq_dec | apply TradeSummaryInformation.eq_dec]. Defined.

  End TradeCancelMessage.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime3.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime3.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime3.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime3.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module Label3.

    (** Label *)
    Record t := {
      symbol : list byte;
      cusip : list byte;
      bsym : list byte;
      sub_product_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 14 /\
      Datatypes.length (cusip record) = 9 /\
      Datatypes.length (bsym record) = 12 /\
      Datatypes.length (sub_product_type record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (symbol record) ++
      encode_bytes 9 (cusip record) ++
      encode_bytes 12 (bsym record) ++
      encode_bytes 5 (sub_product_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (cusip_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (bsym_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (sub_product_type_value, bytes) =>
                      Some ({| symbol := symbol_value; cusip := cusip_value; bsym := bsym_value; sub_product_type := sub_product_type_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End Label3.

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
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End ExecutionDatetime3.

  Module SettlementDate3.

    (** Settlement Date *)
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

  End SettlementDate3.

  Module OriginalTradeInformation2.

    (** Original Trade Information *)
    Record t := {
      quantity_indicator : list byte;
      quantity : list byte;
      price : list byte;
      remuneration : list byte;
      special_price_indicator : list byte;
      side : list byte;
      as_of_indicator : list byte;
      execution_datetime : ExecutionDatetime3.t;
      future_use : list byte;
      sale_condition_3 : list byte;
      sale_condition_4 : list byte;
      settlement_date : SettlementDate3.t;
      yield_direction : list byte;
      yield : list byte;
      when_issued_indicator : list byte;
      reporting_party_type : list byte;
      contra_party_type : list byte;
      ats_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (quantity_indicator record) = 1 /\
      Datatypes.length (quantity record) = 14 /\
      Datatypes.length (price record) = 11 /\
      Datatypes.length (remuneration record) = 1 /\
      Datatypes.length (special_price_indicator record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (as_of_indicator record) = 1 /\
      ExecutionDatetime3.bounded (execution_datetime record) /\
      Datatypes.length (future_use record) = 2 /\
      Datatypes.length (sale_condition_3 record) = 1 /\
      Datatypes.length (sale_condition_4 record) = 1 /\
      SettlementDate3.bounded (settlement_date record) /\
      Datatypes.length (yield_direction record) = 1 /\
      Datatypes.length (yield record) = 13 /\
      Datatypes.length (when_issued_indicator record) = 1 /\
      Datatypes.length (reporting_party_type record) = 1 /\
      Datatypes.length (contra_party_type record) = 1 /\
      Datatypes.length (ats_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (quantity_indicator record) ++
      encode_bytes 14 (quantity record) ++
      encode_bytes 11 (price record) ++
      encode_bytes 1 (remuneration record) ++
      encode_bytes 1 (special_price_indicator record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (as_of_indicator record) ++
      ExecutionDatetime3.encode (execution_datetime record) ++
      encode_bytes 2 (future_use record) ++
      encode_bytes 1 (sale_condition_3 record) ++
      encode_bytes 1 (sale_condition_4 record) ++
      SettlementDate3.encode (settlement_date record) ++
      encode_bytes 1 (yield_direction record) ++
      encode_bytes 13 (yield record) ++
      encode_bytes 1 (when_issued_indicator record) ++
      encode_bytes 1 (reporting_party_type record) ++
      encode_bytes 1 (contra_party_type record) ++
      encode_bytes 1 (ats_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (quantity_indicator_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (quantity_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (remuneration_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (special_price_indicator_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (as_of_indicator_value, bytes) =>
                                  match ExecutionDatetime3.decode bytes with
                                  | None => None
                                  | Some (execution_datetime_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (future_use_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (sale_condition_3_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (sale_condition_4_value, bytes) =>
                                                  match SettlementDate3.decode bytes with
                                                  | None => None
                                                  | Some (settlement_date_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (yield_direction_value, bytes) =>
                                                          match decode_bytes 13 bytes with
                                                          | None => None
                                                          | Some (yield_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (when_issued_indicator_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (reporting_party_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (contra_party_type_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (ats_indicator_value, bytes) =>
                                                                              Some ({| quantity_indicator := quantity_indicator_value; quantity := quantity_value; price := price_value; remuneration := remuneration_value; special_price_indicator := special_price_indicator_value; side := side_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; future_use := future_use_value; sale_condition_3 := sale_condition_3_value; sale_condition_4 := sale_condition_4_value; settlement_date := settlement_date_value; yield_direction := yield_direction_value; yield := yield_value; when_issued_indicator := when_issued_indicator_value; reporting_party_type := reporting_party_type_value; contra_party_type := contra_party_type_value; ats_indicator := ats_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime3.encode_length, !SettlementDate3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite ExecutionDatetime3.decode_encode by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite SettlementDate3.decode_encode by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime3.eq_dec | apply SettlementDate3.eq_dec]. Defined.

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
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End ExecutionDatetime4.

  Module SettlementDate4.

    (** Settlement Date *)
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

  End SettlementDate4.

  Module CorrectionTradeInformation.

    (** Correction Trade Information *)
    Record t := {
      quantity_indicator : list byte;
      quantity : list byte;
      price : list byte;
      remuneration : list byte;
      special_price_indicator : list byte;
      side : list byte;
      as_of_indicator : list byte;
      execution_datetime : ExecutionDatetime4.t;
      future_use : list byte;
      sale_condition_3 : list byte;
      sale_condition_4 : list byte;
      settlement_date : SettlementDate4.t;
      yield_direction : list byte;
      yield : list byte;
      when_issued_indicator : list byte;
      reporting_party_type : list byte;
      contra_party_type : list byte;
      ats_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (quantity_indicator record) = 1 /\
      Datatypes.length (quantity record) = 14 /\
      Datatypes.length (price record) = 11 /\
      Datatypes.length (remuneration record) = 1 /\
      Datatypes.length (special_price_indicator record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (as_of_indicator record) = 1 /\
      ExecutionDatetime4.bounded (execution_datetime record) /\
      Datatypes.length (future_use record) = 2 /\
      Datatypes.length (sale_condition_3 record) = 1 /\
      Datatypes.length (sale_condition_4 record) = 1 /\
      SettlementDate4.bounded (settlement_date record) /\
      Datatypes.length (yield_direction record) = 1 /\
      Datatypes.length (yield record) = 13 /\
      Datatypes.length (when_issued_indicator record) = 1 /\
      Datatypes.length (reporting_party_type record) = 1 /\
      Datatypes.length (contra_party_type record) = 1 /\
      Datatypes.length (ats_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (quantity_indicator record) ++
      encode_bytes 14 (quantity record) ++
      encode_bytes 11 (price record) ++
      encode_bytes 1 (remuneration record) ++
      encode_bytes 1 (special_price_indicator record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (as_of_indicator record) ++
      ExecutionDatetime4.encode (execution_datetime record) ++
      encode_bytes 2 (future_use record) ++
      encode_bytes 1 (sale_condition_3 record) ++
      encode_bytes 1 (sale_condition_4 record) ++
      SettlementDate4.encode (settlement_date record) ++
      encode_bytes 1 (yield_direction record) ++
      encode_bytes 13 (yield record) ++
      encode_bytes 1 (when_issued_indicator record) ++
      encode_bytes 1 (reporting_party_type record) ++
      encode_bytes 1 (contra_party_type record) ++
      encode_bytes 1 (ats_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (quantity_indicator_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (quantity_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (remuneration_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (special_price_indicator_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (as_of_indicator_value, bytes) =>
                                  match ExecutionDatetime4.decode bytes with
                                  | None => None
                                  | Some (execution_datetime_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (future_use_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (sale_condition_3_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (sale_condition_4_value, bytes) =>
                                                  match SettlementDate4.decode bytes with
                                                  | None => None
                                                  | Some (settlement_date_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (yield_direction_value, bytes) =>
                                                          match decode_bytes 13 bytes with
                                                          | None => None
                                                          | Some (yield_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (when_issued_indicator_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (reporting_party_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (contra_party_type_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (ats_indicator_value, bytes) =>
                                                                              Some ({| quantity_indicator := quantity_indicator_value; quantity := quantity_value; price := price_value; remuneration := remuneration_value; special_price_indicator := special_price_indicator_value; side := side_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; future_use := future_use_value; sale_condition_3 := sale_condition_3_value; sale_condition_4 := sale_condition_4_value; settlement_date := settlement_date_value; yield_direction := yield_direction_value; yield := yield_value; when_issued_indicator := when_issued_indicator_value; reporting_party_type := reporting_party_type_value; contra_party_type := contra_party_type_value; ats_indicator := ats_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime4.encode_length, !SettlementDate4.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite ExecutionDatetime4.decode_encode by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite SettlementDate4.decode_encode by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime4.eq_dec | apply SettlementDate4.eq_dec]. Defined.

  End CorrectionTradeInformation.

  Module TradeSummaryInformation2.

    (** Trade Summary Information *)
    Record t := {
      high_price : list byte;
      high_yield_direction : list byte;
      high_yield : list byte;
      low_price : list byte;
      low_yield_direction : list byte;
      low_yield : list byte;
      last_sale_price : list byte;
      last_sale_yield_direction : list byte;
      last_sale_yield : list byte;
      change_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (high_price record) = 11 /\
      Datatypes.length (high_yield_direction record) = 1 /\
      Datatypes.length (high_yield record) = 13 /\
      Datatypes.length (low_price record) = 11 /\
      Datatypes.length (low_yield_direction record) = 1 /\
      Datatypes.length (low_yield record) = 13 /\
      Datatypes.length (last_sale_price record) = 11 /\
      Datatypes.length (last_sale_yield_direction record) = 1 /\
      Datatypes.length (last_sale_yield record) = 13 /\
      Datatypes.length (change_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (high_price record) ++
      encode_bytes 1 (high_yield_direction record) ++
      encode_bytes 13 (high_yield record) ++
      encode_bytes 11 (low_price record) ++
      encode_bytes 1 (low_yield_direction record) ++
      encode_bytes 13 (low_yield record) ++
      encode_bytes 11 (last_sale_price record) ++
      encode_bytes 1 (last_sale_yield_direction record) ++
      encode_bytes 13 (last_sale_yield record) ++
      encode_bytes 1 (change_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_yield_direction_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (high_yield_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (low_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (low_yield_direction_value, bytes) =>
                          match decode_bytes 13 bytes with
                          | None => None
                          | Some (low_yield_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (last_sale_price_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (last_sale_yield_direction_value, bytes) =>
                                      match decode_bytes 13 bytes with
                                      | None => None
                                      | Some (last_sale_yield_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (change_indicator_value, bytes) =>
                                              Some ({| high_price := high_price_value; high_yield_direction := high_yield_direction_value; high_yield := high_yield_value; low_price := low_price_value; low_yield_direction := low_yield_direction_value; low_yield := low_yield_value; last_sale_price := last_sale_price_value; last_sale_yield_direction := last_sale_yield_direction_value; last_sale_yield := last_sale_yield_value; change_indicator := change_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeSummaryInformation2.

  Module TradeCorrectionMessage.

    (** Used to transmit trade correction data from a transaction that was entered either earlier in the day or within the past 19 business days *)
    Record t := {
      message_header : MessageHeader3.t;
      label : Label3.t;
      original_dissemination_date : OriginalDisseminationDate3.t;
      original_trade_identifier : list byte;
      report_function : list byte;
      original_trade_information : OriginalTradeInformation2.t;
      correction_trade_information : CorrectionTradeInformation.t;
      trade_summary_information : TradeSummaryInformation2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader3.bounded (message_header record) /\
      Label3.bounded (label record) /\
      OriginalDisseminationDate3.bounded (original_dissemination_date record) /\
      Datatypes.length (original_trade_identifier record) = 7 /\
      Datatypes.length (report_function record) = 1 /\
      OriginalTradeInformation2.bounded (original_trade_information record) /\
      CorrectionTradeInformation.bounded (correction_trade_information record) /\
      TradeSummaryInformation2.bounded (trade_summary_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader3.encode (message_header record) ++
      Label3.encode (label record) ++
      OriginalDisseminationDate3.encode (original_dissemination_date record) ++
      encode_bytes 7 (original_trade_identifier record) ++
      encode_bytes 1 (report_function record) ++
      OriginalTradeInformation2.encode (original_trade_information record) ++
      CorrectionTradeInformation.encode (correction_trade_information record) ++
      TradeSummaryInformation2.encode (trade_summary_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader3.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match Label3.decode bytes with
          | None => None
          | Some (label_value, bytes) =>
              match OriginalDisseminationDate3.decode bytes with
              | None => None
              | Some (original_dissemination_date_value, bytes) =>
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (original_trade_identifier_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (report_function_value, bytes) =>
                          match OriginalTradeInformation2.decode bytes with
                          | None => None
                          | Some (original_trade_information_value, bytes) =>
                              match CorrectionTradeInformation.decode bytes with
                              | None => None
                              | Some (correction_trade_information_value, bytes) =>
                                  match TradeSummaryInformation2.decode bytes with
                                  | None => None
                                  | Some (trade_summary_information_value, bytes) =>
                                      Some ({| message_header := message_header_value; label := label_value; original_dissemination_date := original_dissemination_date_value; original_trade_identifier := original_trade_identifier_value; report_function := report_function_value; original_trade_information := original_trade_information_value; correction_trade_information := correction_trade_information_value; trade_summary_information := trade_summary_information_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 302.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader3.encode_length, !Label3.encode_length, !OriginalDisseminationDate3.encode_length, !encode_bytes_length, !OriginalTradeInformation2.encode_length, !CorrectionTradeInformation.encode_length, !TradeSummaryInformation2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader3.decode_encode by exact bound_0.
      rewrite Label3.decode_encode by exact bound_1.
      rewrite OriginalDisseminationDate3.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite OriginalTradeInformation2.decode_encode by exact bound_5.
      rewrite CorrectionTradeInformation.decode_encode by exact bound_6.
      rewrite TradeSummaryInformation2.decode_encode by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader3.eq_dec | apply Label3.eq_dec | apply OriginalDisseminationDate3.eq_dec | apply OriginalTradeInformation2.eq_dec | apply CorrectionTradeInformation.eq_dec | apply TradeSummaryInformation2.eq_dec]. Defined.

  End TradeCorrectionMessage.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime4.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime4.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime4.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime4.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module Label4.

    (** Label *)
    Record t := {
      symbol : list byte;
      cusip : list byte;
      bsym : list byte;
      sub_product_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 14 /\
      Datatypes.length (cusip record) = 9 /\
      Datatypes.length (bsym record) = 12 /\
      Datatypes.length (sub_product_type record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (symbol record) ++
      encode_bytes 9 (cusip record) ++
      encode_bytes 12 (bsym record) ++
      encode_bytes 5 (sub_product_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (cusip_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (bsym_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (sub_product_type_value, bytes) =>
                      Some ({| symbol := symbol_value; cusip := cusip_value; bsym := bsym_value; sub_product_type := sub_product_type_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End Label4.

  Module DailyTradeSummaryMessage.

    (** Price summary message disseminated for each agency debt security that traded during the day during the normal trading hours *)
    Record t := {
      message_header : MessageHeader4.t;
      label : Label4.t;
      when_issued_indicator : list byte;
      daily_high_price : list byte;
      high_yield_direction : list byte;
      daily_high_yield : list byte;
      daily_low_price : list byte;
      low_yield_direction : list byte;
      daily_low_yield : list byte;
      daily_close_price : list byte;
      close_yield_direction : list byte;
      daily_close_yield : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader4.bounded (message_header record) /\
      Label4.bounded (label record) /\
      Datatypes.length (when_issued_indicator record) = 1 /\
      Datatypes.length (daily_high_price record) = 11 /\
      Datatypes.length (high_yield_direction record) = 1 /\
      Datatypes.length (daily_high_yield record) = 13 /\
      Datatypes.length (daily_low_price record) = 11 /\
      Datatypes.length (low_yield_direction record) = 1 /\
      Datatypes.length (daily_low_yield record) = 13 /\
      Datatypes.length (daily_close_price record) = 11 /\
      Datatypes.length (close_yield_direction record) = 1 /\
      Datatypes.length (daily_close_yield record) = 13.

    Definition encode (record : t) : list byte :=
      MessageHeader4.encode (message_header record) ++
      Label4.encode (label record) ++
      encode_bytes 1 (when_issued_indicator record) ++
      encode_bytes 11 (daily_high_price record) ++
      encode_bytes 1 (high_yield_direction record) ++
      encode_bytes 13 (daily_high_yield record) ++
      encode_bytes 11 (daily_low_price record) ++
      encode_bytes 1 (low_yield_direction record) ++
      encode_bytes 13 (daily_low_yield record) ++
      encode_bytes 11 (daily_close_price record) ++
      encode_bytes 1 (close_yield_direction record) ++
      encode_bytes 13 (daily_close_yield record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader4.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match Label4.decode bytes with
          | None => None
          | Some (label_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (when_issued_indicator_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (daily_high_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (high_yield_direction_value, bytes) =>
                          match decode_bytes 13 bytes with
                          | None => None
                          | Some (daily_high_yield_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (daily_low_price_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (low_yield_direction_value, bytes) =>
                                      match decode_bytes 13 bytes with
                                      | None => None
                                      | Some (daily_low_yield_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (daily_close_price_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (close_yield_direction_value, bytes) =>
                                                  match decode_bytes 13 bytes with
                                                  | None => None
                                                  | Some (daily_close_yield_value, bytes) =>
                                                      Some ({| message_header := message_header_value; label := label_value; when_issued_indicator := when_issued_indicator_value; daily_high_price := daily_high_price_value; high_yield_direction := high_yield_direction_value; daily_high_yield := daily_high_yield_value; daily_low_price := daily_low_price_value; low_yield_direction := low_yield_direction_value; daily_low_yield := daily_low_yield_value; daily_close_price := daily_close_price_value; close_yield_direction := close_yield_direction_value; daily_close_yield := daily_close_yield_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 138.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader4.encode_length, !Label4.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader4.decode_encode by exact bound_0.
      rewrite Label4.decode_encode by exact bound_1.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader4.eq_dec | apply Label4.eq_dec]. Defined.

  End DailyTradeSummaryMessage.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime5.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime5.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime5.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime5.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module Label5.

    (** Label *)
    Record t := {
      symbol : list byte;
      cusip : list byte;
      bsym : list byte;
      sub_product_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 14 /\
      Datatypes.length (cusip record) = 9 /\
      Datatypes.length (bsym record) = 12 /\
      Datatypes.length (sub_product_type record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (symbol record) ++
      encode_bytes 9 (cusip record) ++
      encode_bytes 12 (bsym record) ++
      encode_bytes 5 (sub_product_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (cusip_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (bsym_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (sub_product_type_value, bytes) =>
                      Some ({| symbol := symbol_value; cusip := cusip_value; bsym := bsym_value; sub_product_type := sub_product_type_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End Label5.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  Module TradingHaltMessage.

    (** Disseminated when a trading halt is instituted or removed for an agency debt security *)
    Record t := {
      message_header : MessageHeader5.t;
      label : Label5.t;
      issuer : list byte;
      action : list byte;
      action_datetime : ActionDatetime.t;
      halt_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader5.bounded (message_header record) /\
      Label5.bounded (label record) /\
      Datatypes.length (issuer record) = 30 /\
      Datatypes.length (action record) = 1 /\
      ActionDatetime.bounded (action_datetime record) /\
      Datatypes.length (halt_reason record) = 4.

    Definition encode (record : t) : list byte :=
      MessageHeader5.encode (message_header record) ++
      Label5.encode (label record) ++
      encode_bytes 30 (issuer record) ++
      encode_bytes 1 (action record) ++
      ActionDatetime.encode (action_datetime record) ++
      encode_bytes 4 (halt_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader5.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match Label5.decode bytes with
          | None => None
          | Some (label_value, bytes) =>
              match decode_bytes 30 bytes with
              | None => None
              | Some (issuer_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (action_value, bytes) =>
                      match ActionDatetime.decode bytes with
                      | None => None
                      | Some (action_datetime_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (halt_reason_value, bytes) =>
                              Some ({| message_header := message_header_value; label := label_value; issuer := issuer_value; action := action_value; action_datetime := action_datetime_value; halt_reason := halt_reason_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 111.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader5.encode_length, !Label5.encode_length, !encode_bytes_length, !ActionDatetime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader5.decode_encode by exact bound_0.
      rewrite Label5.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite ActionDatetime.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader5.eq_dec | apply Label5.eq_dec | apply ActionDatetime.eq_dec]. Defined.

  End TradingHaltMessage.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime6.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime6.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime6.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime6.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime7.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime7.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime7.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime7.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module MarketBreadthInformation.

    (** Market Breadth Information *)
    Record t := {
      total_securities_traded_all_securities : list byte;
      total_securities_traded_freddie_mac : list byte;
      total_securities_traded_fannie_mae : list byte;
      total_securities_traded_fhlb : list byte;
      advances_all_securities : list byte;
      advances_freddie_mac : list byte;
      advances_fannie_mae : list byte;
      advances_fhlb : list byte;
      declines_all_securities : list byte;
      declines_freddie_mac : list byte;
      declines_fannie_mae : list byte;
      declines_fhlb : list byte;
      unchanged_all_securities : list byte;
      unchanged_freddie_mac : list byte;
      unchanged_fannie_mae : list byte;
      unchanged_fhlb : list byte;
      fifty_two_week_high_all_securities : list byte;
      fifty_two_week_high_freddie_mac : list byte;
      fifty_two_week_high_fannie_mae : list byte;
      fifty_two_week_high_fhlb : list byte;
      fifty_two_week_low_all_securities : list byte;
      fifty_two_week_low_freddie_mac : list byte;
      fifty_two_week_low_fannie_mae : list byte;
      fifty_two_week_low_fhlb : list byte;
      total_volume_all_securities : list byte;
      total_volume_freddie_mac : list byte;
      total_volume_fannie_mae : list byte;
      total_volume_fhlb : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (total_securities_traded_all_securities record) = 6 /\
      Datatypes.length (total_securities_traded_freddie_mac record) = 6 /\
      Datatypes.length (total_securities_traded_fannie_mae record) = 6 /\
      Datatypes.length (total_securities_traded_fhlb record) = 6 /\
      Datatypes.length (advances_all_securities record) = 6 /\
      Datatypes.length (advances_freddie_mac record) = 6 /\
      Datatypes.length (advances_fannie_mae record) = 6 /\
      Datatypes.length (advances_fhlb record) = 6 /\
      Datatypes.length (declines_all_securities record) = 6 /\
      Datatypes.length (declines_freddie_mac record) = 6 /\
      Datatypes.length (declines_fannie_mae record) = 6 /\
      Datatypes.length (declines_fhlb record) = 6 /\
      Datatypes.length (unchanged_all_securities record) = 6 /\
      Datatypes.length (unchanged_freddie_mac record) = 6 /\
      Datatypes.length (unchanged_fannie_mae record) = 6 /\
      Datatypes.length (unchanged_fhlb record) = 6 /\
      Datatypes.length (fifty_two_week_high_all_securities record) = 6 /\
      Datatypes.length (fifty_two_week_high_freddie_mac record) = 6 /\
      Datatypes.length (fifty_two_week_high_fannie_mae record) = 6 /\
      Datatypes.length (fifty_two_week_high_fhlb record) = 6 /\
      Datatypes.length (fifty_two_week_low_all_securities record) = 6 /\
      Datatypes.length (fifty_two_week_low_freddie_mac record) = 6 /\
      Datatypes.length (fifty_two_week_low_fannie_mae record) = 6 /\
      Datatypes.length (fifty_two_week_low_fhlb record) = 6 /\
      Datatypes.length (total_volume_all_securities record) = 13 /\
      Datatypes.length (total_volume_freddie_mac record) = 13 /\
      Datatypes.length (total_volume_fannie_mae record) = 13 /\
      Datatypes.length (total_volume_fhlb record) = 13.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (total_securities_traded_all_securities record) ++
      encode_bytes 6 (total_securities_traded_freddie_mac record) ++
      encode_bytes 6 (total_securities_traded_fannie_mae record) ++
      encode_bytes 6 (total_securities_traded_fhlb record) ++
      encode_bytes 6 (advances_all_securities record) ++
      encode_bytes 6 (advances_freddie_mac record) ++
      encode_bytes 6 (advances_fannie_mae record) ++
      encode_bytes 6 (advances_fhlb record) ++
      encode_bytes 6 (declines_all_securities record) ++
      encode_bytes 6 (declines_freddie_mac record) ++
      encode_bytes 6 (declines_fannie_mae record) ++
      encode_bytes 6 (declines_fhlb record) ++
      encode_bytes 6 (unchanged_all_securities record) ++
      encode_bytes 6 (unchanged_freddie_mac record) ++
      encode_bytes 6 (unchanged_fannie_mae record) ++
      encode_bytes 6 (unchanged_fhlb record) ++
      encode_bytes 6 (fifty_two_week_high_all_securities record) ++
      encode_bytes 6 (fifty_two_week_high_freddie_mac record) ++
      encode_bytes 6 (fifty_two_week_high_fannie_mae record) ++
      encode_bytes 6 (fifty_two_week_high_fhlb record) ++
      encode_bytes 6 (fifty_two_week_low_all_securities record) ++
      encode_bytes 6 (fifty_two_week_low_freddie_mac record) ++
      encode_bytes 6 (fifty_two_week_low_fannie_mae record) ++
      encode_bytes 6 (fifty_two_week_low_fhlb record) ++
      encode_bytes 13 (total_volume_all_securities record) ++
      encode_bytes 13 (total_volume_freddie_mac record) ++
      encode_bytes 13 (total_volume_fannie_mae record) ++
      encode_bytes 13 (total_volume_fhlb record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (total_securities_traded_all_securities_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (total_securities_traded_freddie_mac_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (total_securities_traded_fannie_mae_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (total_securities_traded_fhlb_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (advances_all_securities_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (advances_freddie_mac_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (advances_fannie_mae_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (advances_fhlb_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (declines_all_securities_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (declines_freddie_mac_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (declines_fannie_mae_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (declines_fhlb_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (unchanged_all_securities_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (unchanged_freddie_mac_value, bytes) =>
                                                              match decode_bytes 6 bytes with
                                                              | None => None
                                                              | Some (unchanged_fannie_mae_value, bytes) =>
                                                                  match decode_bytes 6 bytes with
                                                                  | None => None
                                                                  | Some (unchanged_fhlb_value, bytes) =>
                                                                      match decode_bytes 6 bytes with
                                                                      | None => None
                                                                      | Some (fifty_two_week_high_all_securities_value, bytes) =>
                                                                          match decode_bytes 6 bytes with
                                                                          | None => None
                                                                          | Some (fifty_two_week_high_freddie_mac_value, bytes) =>
                                                                              match decode_bytes 6 bytes with
                                                                              | None => None
                                                                              | Some (fifty_two_week_high_fannie_mae_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (fifty_two_week_high_fhlb_value, bytes) =>
                                                                                      match decode_bytes 6 bytes with
                                                                                      | None => None
                                                                                      | Some (fifty_two_week_low_all_securities_value, bytes) =>
                                                                                          match decode_bytes 6 bytes with
                                                                                          | None => None
                                                                                          | Some (fifty_two_week_low_freddie_mac_value, bytes) =>
                                                                                              match decode_bytes 6 bytes with
                                                                                              | None => None
                                                                                              | Some (fifty_two_week_low_fannie_mae_value, bytes) =>
                                                                                                  match decode_bytes 6 bytes with
                                                                                                  | None => None
                                                                                                  | Some (fifty_two_week_low_fhlb_value, bytes) =>
                                                                                                      match decode_bytes 13 bytes with
                                                                                                      | None => None
                                                                                                      | Some (total_volume_all_securities_value, bytes) =>
                                                                                                          match decode_bytes 13 bytes with
                                                                                                          | None => None
                                                                                                          | Some (total_volume_freddie_mac_value, bytes) =>
                                                                                                              match decode_bytes 13 bytes with
                                                                                                              | None => None
                                                                                                              | Some (total_volume_fannie_mae_value, bytes) =>
                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (total_volume_fhlb_value, bytes) =>
                                                                                                                      Some ({| total_securities_traded_all_securities := total_securities_traded_all_securities_value; total_securities_traded_freddie_mac := total_securities_traded_freddie_mac_value; total_securities_traded_fannie_mae := total_securities_traded_fannie_mae_value; total_securities_traded_fhlb := total_securities_traded_fhlb_value; advances_all_securities := advances_all_securities_value; advances_freddie_mac := advances_freddie_mac_value; advances_fannie_mae := advances_fannie_mae_value; advances_fhlb := advances_fhlb_value; declines_all_securities := declines_all_securities_value; declines_freddie_mac := declines_freddie_mac_value; declines_fannie_mae := declines_fannie_mae_value; declines_fhlb := declines_fhlb_value; unchanged_all_securities := unchanged_all_securities_value; unchanged_freddie_mac := unchanged_freddie_mac_value; unchanged_fannie_mae := unchanged_fannie_mae_value; unchanged_fhlb := unchanged_fhlb_value; fifty_two_week_high_all_securities := fifty_two_week_high_all_securities_value; fifty_two_week_high_freddie_mac := fifty_two_week_high_freddie_mac_value; fifty_two_week_high_fannie_mae := fifty_two_week_high_fannie_mae_value; fifty_two_week_high_fhlb := fifty_two_week_high_fhlb_value; fifty_two_week_low_all_securities := fifty_two_week_low_all_securities_value; fifty_two_week_low_freddie_mac := fifty_two_week_low_freddie_mac_value; fifty_two_week_low_fannie_mae := fifty_two_week_low_fannie_mae_value; fifty_two_week_low_fhlb := fifty_two_week_low_fhlb_value; total_volume_all_securities := total_volume_all_securities_value; total_volume_freddie_mac := total_volume_freddie_mac_value; total_volume_fannie_mae := total_volume_fannie_mae_value; total_volume_fhlb := total_volume_fhlb_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 196.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketBreadthInformation.

  Module MarketBreadthMessage.

    (** End of day market breadth aggregate data for Trace eligible publicly traded securities *)
    Record t := {
      message_header : MessageHeader7.t;
      market_breadth_information : MarketBreadthInformation.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader7.bounded (message_header record) /\
      MarketBreadthInformation.bounded (market_breadth_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader7.encode (message_header record) ++
      MarketBreadthInformation.encode (market_breadth_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader7.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match MarketBreadthInformation.decode bytes with
          | None => None
          | Some (market_breadth_information_value, bytes) =>
              Some ({| message_header := message_header_value; market_breadth_information := market_breadth_information_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 218.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader7.encode_length, !MarketBreadthInformation.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader7.decode_encode by exact bound_0.
      rewrite MarketBreadthInformation.decode_encode by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader7.eq_dec | apply MarketBreadthInformation.eq_dec]. Defined.

  End MarketBreadthMessage.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime8.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime8.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime8.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime8.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module MarketSentimentInformation.

    (** Market Sentiment Information *)
    Record t := {
      total_number_of_transactions_all_securities : list byte;
      total_securities_traded_all_securities : list byte;
      total_volume_all_securities : list byte;
      total_number_of_transactions_customer_buy : list byte;
      total_securities_traded_customer_buy : list byte;
      total_volume_customer_buy : list byte;
      total_number_of_transactions_customer_sell : list byte;
      total_securities_traded_customer_sell : list byte;
      total_volume_customer_sell : list byte;
      total_number_of_transactions_affiliate_buy : list byte;
      total_securities_traded_affiliate_buy : list byte;
      total_volume_affiliate_buy : list byte;
      total_number_of_transactions_affiliate_sell : list byte;
      total_securities_traded_affiliate_sell : list byte;
      total_volume_affiliate_sell : list byte;
      total_number_of_transactions_inter_dealer : list byte;
      total_securities_traded_inter_dealer : list byte;
      total_volume_inter_dealer : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (total_number_of_transactions_all_securities record) = 6 /\
      Datatypes.length (total_securities_traded_all_securities record) = 6 /\
      Datatypes.length (total_volume_all_securities record) = 13 /\
      Datatypes.length (total_number_of_transactions_customer_buy record) = 6 /\
      Datatypes.length (total_securities_traded_customer_buy record) = 6 /\
      Datatypes.length (total_volume_customer_buy record) = 13 /\
      Datatypes.length (total_number_of_transactions_customer_sell record) = 6 /\
      Datatypes.length (total_securities_traded_customer_sell record) = 6 /\
      Datatypes.length (total_volume_customer_sell record) = 13 /\
      Datatypes.length (total_number_of_transactions_affiliate_buy record) = 6 /\
      Datatypes.length (total_securities_traded_affiliate_buy record) = 6 /\
      Datatypes.length (total_volume_affiliate_buy record) = 13 /\
      Datatypes.length (total_number_of_transactions_affiliate_sell record) = 6 /\
      Datatypes.length (total_securities_traded_affiliate_sell record) = 6 /\
      Datatypes.length (total_volume_affiliate_sell record) = 13 /\
      Datatypes.length (total_number_of_transactions_inter_dealer record) = 6 /\
      Datatypes.length (total_securities_traded_inter_dealer record) = 6 /\
      Datatypes.length (total_volume_inter_dealer record) = 13.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (total_number_of_transactions_all_securities record) ++
      encode_bytes 6 (total_securities_traded_all_securities record) ++
      encode_bytes 13 (total_volume_all_securities record) ++
      encode_bytes 6 (total_number_of_transactions_customer_buy record) ++
      encode_bytes 6 (total_securities_traded_customer_buy record) ++
      encode_bytes 13 (total_volume_customer_buy record) ++
      encode_bytes 6 (total_number_of_transactions_customer_sell record) ++
      encode_bytes 6 (total_securities_traded_customer_sell record) ++
      encode_bytes 13 (total_volume_customer_sell record) ++
      encode_bytes 6 (total_number_of_transactions_affiliate_buy record) ++
      encode_bytes 6 (total_securities_traded_affiliate_buy record) ++
      encode_bytes 13 (total_volume_affiliate_buy record) ++
      encode_bytes 6 (total_number_of_transactions_affiliate_sell record) ++
      encode_bytes 6 (total_securities_traded_affiliate_sell record) ++
      encode_bytes 13 (total_volume_affiliate_sell record) ++
      encode_bytes 6 (total_number_of_transactions_inter_dealer record) ++
      encode_bytes 6 (total_securities_traded_inter_dealer record) ++
      encode_bytes 13 (total_volume_inter_dealer record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (total_number_of_transactions_all_securities_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (total_securities_traded_all_securities_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (total_volume_all_securities_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (total_number_of_transactions_customer_buy_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (total_securities_traded_customer_buy_value, bytes) =>
                          match decode_bytes 13 bytes with
                          | None => None
                          | Some (total_volume_customer_buy_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (total_number_of_transactions_customer_sell_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (total_securities_traded_customer_sell_value, bytes) =>
                                      match decode_bytes 13 bytes with
                                      | None => None
                                      | Some (total_volume_customer_sell_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (total_number_of_transactions_affiliate_buy_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (total_securities_traded_affiliate_buy_value, bytes) =>
                                                  match decode_bytes 13 bytes with
                                                  | None => None
                                                  | Some (total_volume_affiliate_buy_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (total_number_of_transactions_affiliate_sell_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (total_securities_traded_affiliate_sell_value, bytes) =>
                                                              match decode_bytes 13 bytes with
                                                              | None => None
                                                              | Some (total_volume_affiliate_sell_value, bytes) =>
                                                                  match decode_bytes 6 bytes with
                                                                  | None => None
                                                                  | Some (total_number_of_transactions_inter_dealer_value, bytes) =>
                                                                      match decode_bytes 6 bytes with
                                                                      | None => None
                                                                      | Some (total_securities_traded_inter_dealer_value, bytes) =>
                                                                          match decode_bytes 13 bytes with
                                                                          | None => None
                                                                          | Some (total_volume_inter_dealer_value, bytes) =>
                                                                              Some ({| total_number_of_transactions_all_securities := total_number_of_transactions_all_securities_value; total_securities_traded_all_securities := total_securities_traded_all_securities_value; total_volume_all_securities := total_volume_all_securities_value; total_number_of_transactions_customer_buy := total_number_of_transactions_customer_buy_value; total_securities_traded_customer_buy := total_securities_traded_customer_buy_value; total_volume_customer_buy := total_volume_customer_buy_value; total_number_of_transactions_customer_sell := total_number_of_transactions_customer_sell_value; total_securities_traded_customer_sell := total_securities_traded_customer_sell_value; total_volume_customer_sell := total_volume_customer_sell_value; total_number_of_transactions_affiliate_buy := total_number_of_transactions_affiliate_buy_value; total_securities_traded_affiliate_buy := total_securities_traded_affiliate_buy_value; total_volume_affiliate_buy := total_volume_affiliate_buy_value; total_number_of_transactions_affiliate_sell := total_number_of_transactions_affiliate_sell_value; total_securities_traded_affiliate_sell := total_securities_traded_affiliate_sell_value; total_volume_affiliate_sell := total_volume_affiliate_sell_value; total_number_of_transactions_inter_dealer := total_number_of_transactions_inter_dealer_value; total_securities_traded_inter_dealer := total_securities_traded_inter_dealer_value; total_volume_inter_dealer := total_volume_inter_dealer_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 150.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSentimentInformation.

  Module MarketSentimentAllSecuritiesMessage.

    (** End of day market sentiment aggregate data for all securities *)
    Record t := {
      message_header : MessageHeader8.t;
      market_sentiment_information : MarketSentimentInformation.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader8.bounded (message_header record) /\
      MarketSentimentInformation.bounded (market_sentiment_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader8.encode (message_header record) ++
      MarketSentimentInformation.encode (market_sentiment_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader8.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match MarketSentimentInformation.decode bytes with
          | None => None
          | Some (market_sentiment_information_value, bytes) =>
              Some ({| message_header := message_header_value; market_sentiment_information := market_sentiment_information_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 172.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader8.encode_length, !MarketSentimentInformation.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader8.decode_encode by exact bound_0.
      rewrite MarketSentimentInformation.decode_encode by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader8.eq_dec | apply MarketSentimentInformation.eq_dec]. Defined.

  End MarketSentimentAllSecuritiesMessage.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime9.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime9.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime9.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime9.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module MarketSentimentInformation2.

    (** Market Sentiment Information *)
    Record t := {
      total_number_of_transactions_all_securities : list byte;
      total_securities_traded_all_securities : list byte;
      total_volume_all_securities : list byte;
      total_number_of_transactions_customer_buy : list byte;
      total_securities_traded_customer_buy : list byte;
      total_volume_customer_buy : list byte;
      total_number_of_transactions_customer_sell : list byte;
      total_securities_traded_customer_sell : list byte;
      total_volume_customer_sell : list byte;
      total_number_of_transactions_affiliate_buy : list byte;
      total_securities_traded_affiliate_buy : list byte;
      total_volume_affiliate_buy : list byte;
      total_number_of_transactions_affiliate_sell : list byte;
      total_securities_traded_affiliate_sell : list byte;
      total_volume_affiliate_sell : list byte;
      total_number_of_transactions_inter_dealer : list byte;
      total_securities_traded_inter_dealer : list byte;
      total_volume_inter_dealer : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (total_number_of_transactions_all_securities record) = 6 /\
      Datatypes.length (total_securities_traded_all_securities record) = 6 /\
      Datatypes.length (total_volume_all_securities record) = 13 /\
      Datatypes.length (total_number_of_transactions_customer_buy record) = 6 /\
      Datatypes.length (total_securities_traded_customer_buy record) = 6 /\
      Datatypes.length (total_volume_customer_buy record) = 13 /\
      Datatypes.length (total_number_of_transactions_customer_sell record) = 6 /\
      Datatypes.length (total_securities_traded_customer_sell record) = 6 /\
      Datatypes.length (total_volume_customer_sell record) = 13 /\
      Datatypes.length (total_number_of_transactions_affiliate_buy record) = 6 /\
      Datatypes.length (total_securities_traded_affiliate_buy record) = 6 /\
      Datatypes.length (total_volume_affiliate_buy record) = 13 /\
      Datatypes.length (total_number_of_transactions_affiliate_sell record) = 6 /\
      Datatypes.length (total_securities_traded_affiliate_sell record) = 6 /\
      Datatypes.length (total_volume_affiliate_sell record) = 13 /\
      Datatypes.length (total_number_of_transactions_inter_dealer record) = 6 /\
      Datatypes.length (total_securities_traded_inter_dealer record) = 6 /\
      Datatypes.length (total_volume_inter_dealer record) = 13.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (total_number_of_transactions_all_securities record) ++
      encode_bytes 6 (total_securities_traded_all_securities record) ++
      encode_bytes 13 (total_volume_all_securities record) ++
      encode_bytes 6 (total_number_of_transactions_customer_buy record) ++
      encode_bytes 6 (total_securities_traded_customer_buy record) ++
      encode_bytes 13 (total_volume_customer_buy record) ++
      encode_bytes 6 (total_number_of_transactions_customer_sell record) ++
      encode_bytes 6 (total_securities_traded_customer_sell record) ++
      encode_bytes 13 (total_volume_customer_sell record) ++
      encode_bytes 6 (total_number_of_transactions_affiliate_buy record) ++
      encode_bytes 6 (total_securities_traded_affiliate_buy record) ++
      encode_bytes 13 (total_volume_affiliate_buy record) ++
      encode_bytes 6 (total_number_of_transactions_affiliate_sell record) ++
      encode_bytes 6 (total_securities_traded_affiliate_sell record) ++
      encode_bytes 13 (total_volume_affiliate_sell record) ++
      encode_bytes 6 (total_number_of_transactions_inter_dealer record) ++
      encode_bytes 6 (total_securities_traded_inter_dealer record) ++
      encode_bytes 13 (total_volume_inter_dealer record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (total_number_of_transactions_all_securities_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (total_securities_traded_all_securities_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (total_volume_all_securities_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (total_number_of_transactions_customer_buy_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (total_securities_traded_customer_buy_value, bytes) =>
                          match decode_bytes 13 bytes with
                          | None => None
                          | Some (total_volume_customer_buy_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (total_number_of_transactions_customer_sell_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (total_securities_traded_customer_sell_value, bytes) =>
                                      match decode_bytes 13 bytes with
                                      | None => None
                                      | Some (total_volume_customer_sell_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (total_number_of_transactions_affiliate_buy_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (total_securities_traded_affiliate_buy_value, bytes) =>
                                                  match decode_bytes 13 bytes with
                                                  | None => None
                                                  | Some (total_volume_affiliate_buy_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (total_number_of_transactions_affiliate_sell_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (total_securities_traded_affiliate_sell_value, bytes) =>
                                                              match decode_bytes 13 bytes with
                                                              | None => None
                                                              | Some (total_volume_affiliate_sell_value, bytes) =>
                                                                  match decode_bytes 6 bytes with
                                                                  | None => None
                                                                  | Some (total_number_of_transactions_inter_dealer_value, bytes) =>
                                                                      match decode_bytes 6 bytes with
                                                                      | None => None
                                                                      | Some (total_securities_traded_inter_dealer_value, bytes) =>
                                                                          match decode_bytes 13 bytes with
                                                                          | None => None
                                                                          | Some (total_volume_inter_dealer_value, bytes) =>
                                                                              Some ({| total_number_of_transactions_all_securities := total_number_of_transactions_all_securities_value; total_securities_traded_all_securities := total_securities_traded_all_securities_value; total_volume_all_securities := total_volume_all_securities_value; total_number_of_transactions_customer_buy := total_number_of_transactions_customer_buy_value; total_securities_traded_customer_buy := total_securities_traded_customer_buy_value; total_volume_customer_buy := total_volume_customer_buy_value; total_number_of_transactions_customer_sell := total_number_of_transactions_customer_sell_value; total_securities_traded_customer_sell := total_securities_traded_customer_sell_value; total_volume_customer_sell := total_volume_customer_sell_value; total_number_of_transactions_affiliate_buy := total_number_of_transactions_affiliate_buy_value; total_securities_traded_affiliate_buy := total_securities_traded_affiliate_buy_value; total_volume_affiliate_buy := total_volume_affiliate_buy_value; total_number_of_transactions_affiliate_sell := total_number_of_transactions_affiliate_sell_value; total_securities_traded_affiliate_sell := total_securities_traded_affiliate_sell_value; total_volume_affiliate_sell := total_volume_affiliate_sell_value; total_number_of_transactions_inter_dealer := total_number_of_transactions_inter_dealer_value; total_securities_traded_inter_dealer := total_securities_traded_inter_dealer_value; total_volume_inter_dealer := total_volume_inter_dealer_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 150.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSentimentInformation2.

  Module MarketSentimentFannieMaeMessage.

    (** End of day market sentiment aggregate data for Fannie Mae issues *)
    Record t := {
      message_header : MessageHeader9.t;
      market_sentiment_information : MarketSentimentInformation2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader9.bounded (message_header record) /\
      MarketSentimentInformation2.bounded (market_sentiment_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader9.encode (message_header record) ++
      MarketSentimentInformation2.encode (market_sentiment_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader9.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match MarketSentimentInformation2.decode bytes with
          | None => None
          | Some (market_sentiment_information_value, bytes) =>
              Some ({| message_header := message_header_value; market_sentiment_information := market_sentiment_information_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 172.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader9.encode_length, !MarketSentimentInformation2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader9.decode_encode by exact bound_0.
      rewrite MarketSentimentInformation2.decode_encode by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader9.eq_dec | apply MarketSentimentInformation2.eq_dec]. Defined.

  End MarketSentimentFannieMaeMessage.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime10.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime10.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime10.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime10.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module MarketSentimentInformation3.

    (** Market Sentiment Information *)
    Record t := {
      total_number_of_transactions_all_securities : list byte;
      total_securities_traded_all_securities : list byte;
      total_volume_all_securities : list byte;
      total_number_of_transactions_customer_buy : list byte;
      total_securities_traded_customer_buy : list byte;
      total_volume_customer_buy : list byte;
      total_number_of_transactions_customer_sell : list byte;
      total_securities_traded_customer_sell : list byte;
      total_volume_customer_sell : list byte;
      total_number_of_transactions_affiliate_buy : list byte;
      total_securities_traded_affiliate_buy : list byte;
      total_volume_affiliate_buy : list byte;
      total_number_of_transactions_affiliate_sell : list byte;
      total_securities_traded_affiliate_sell : list byte;
      total_volume_affiliate_sell : list byte;
      total_number_of_transactions_inter_dealer : list byte;
      total_securities_traded_inter_dealer : list byte;
      total_volume_inter_dealer : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (total_number_of_transactions_all_securities record) = 6 /\
      Datatypes.length (total_securities_traded_all_securities record) = 6 /\
      Datatypes.length (total_volume_all_securities record) = 13 /\
      Datatypes.length (total_number_of_transactions_customer_buy record) = 6 /\
      Datatypes.length (total_securities_traded_customer_buy record) = 6 /\
      Datatypes.length (total_volume_customer_buy record) = 13 /\
      Datatypes.length (total_number_of_transactions_customer_sell record) = 6 /\
      Datatypes.length (total_securities_traded_customer_sell record) = 6 /\
      Datatypes.length (total_volume_customer_sell record) = 13 /\
      Datatypes.length (total_number_of_transactions_affiliate_buy record) = 6 /\
      Datatypes.length (total_securities_traded_affiliate_buy record) = 6 /\
      Datatypes.length (total_volume_affiliate_buy record) = 13 /\
      Datatypes.length (total_number_of_transactions_affiliate_sell record) = 6 /\
      Datatypes.length (total_securities_traded_affiliate_sell record) = 6 /\
      Datatypes.length (total_volume_affiliate_sell record) = 13 /\
      Datatypes.length (total_number_of_transactions_inter_dealer record) = 6 /\
      Datatypes.length (total_securities_traded_inter_dealer record) = 6 /\
      Datatypes.length (total_volume_inter_dealer record) = 13.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (total_number_of_transactions_all_securities record) ++
      encode_bytes 6 (total_securities_traded_all_securities record) ++
      encode_bytes 13 (total_volume_all_securities record) ++
      encode_bytes 6 (total_number_of_transactions_customer_buy record) ++
      encode_bytes 6 (total_securities_traded_customer_buy record) ++
      encode_bytes 13 (total_volume_customer_buy record) ++
      encode_bytes 6 (total_number_of_transactions_customer_sell record) ++
      encode_bytes 6 (total_securities_traded_customer_sell record) ++
      encode_bytes 13 (total_volume_customer_sell record) ++
      encode_bytes 6 (total_number_of_transactions_affiliate_buy record) ++
      encode_bytes 6 (total_securities_traded_affiliate_buy record) ++
      encode_bytes 13 (total_volume_affiliate_buy record) ++
      encode_bytes 6 (total_number_of_transactions_affiliate_sell record) ++
      encode_bytes 6 (total_securities_traded_affiliate_sell record) ++
      encode_bytes 13 (total_volume_affiliate_sell record) ++
      encode_bytes 6 (total_number_of_transactions_inter_dealer record) ++
      encode_bytes 6 (total_securities_traded_inter_dealer record) ++
      encode_bytes 13 (total_volume_inter_dealer record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (total_number_of_transactions_all_securities_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (total_securities_traded_all_securities_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (total_volume_all_securities_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (total_number_of_transactions_customer_buy_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (total_securities_traded_customer_buy_value, bytes) =>
                          match decode_bytes 13 bytes with
                          | None => None
                          | Some (total_volume_customer_buy_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (total_number_of_transactions_customer_sell_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (total_securities_traded_customer_sell_value, bytes) =>
                                      match decode_bytes 13 bytes with
                                      | None => None
                                      | Some (total_volume_customer_sell_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (total_number_of_transactions_affiliate_buy_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (total_securities_traded_affiliate_buy_value, bytes) =>
                                                  match decode_bytes 13 bytes with
                                                  | None => None
                                                  | Some (total_volume_affiliate_buy_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (total_number_of_transactions_affiliate_sell_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (total_securities_traded_affiliate_sell_value, bytes) =>
                                                              match decode_bytes 13 bytes with
                                                              | None => None
                                                              | Some (total_volume_affiliate_sell_value, bytes) =>
                                                                  match decode_bytes 6 bytes with
                                                                  | None => None
                                                                  | Some (total_number_of_transactions_inter_dealer_value, bytes) =>
                                                                      match decode_bytes 6 bytes with
                                                                      | None => None
                                                                      | Some (total_securities_traded_inter_dealer_value, bytes) =>
                                                                          match decode_bytes 13 bytes with
                                                                          | None => None
                                                                          | Some (total_volume_inter_dealer_value, bytes) =>
                                                                              Some ({| total_number_of_transactions_all_securities := total_number_of_transactions_all_securities_value; total_securities_traded_all_securities := total_securities_traded_all_securities_value; total_volume_all_securities := total_volume_all_securities_value; total_number_of_transactions_customer_buy := total_number_of_transactions_customer_buy_value; total_securities_traded_customer_buy := total_securities_traded_customer_buy_value; total_volume_customer_buy := total_volume_customer_buy_value; total_number_of_transactions_customer_sell := total_number_of_transactions_customer_sell_value; total_securities_traded_customer_sell := total_securities_traded_customer_sell_value; total_volume_customer_sell := total_volume_customer_sell_value; total_number_of_transactions_affiliate_buy := total_number_of_transactions_affiliate_buy_value; total_securities_traded_affiliate_buy := total_securities_traded_affiliate_buy_value; total_volume_affiliate_buy := total_volume_affiliate_buy_value; total_number_of_transactions_affiliate_sell := total_number_of_transactions_affiliate_sell_value; total_securities_traded_affiliate_sell := total_securities_traded_affiliate_sell_value; total_volume_affiliate_sell := total_volume_affiliate_sell_value; total_number_of_transactions_inter_dealer := total_number_of_transactions_inter_dealer_value; total_securities_traded_inter_dealer := total_securities_traded_inter_dealer_value; total_volume_inter_dealer := total_volume_inter_dealer_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 150.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSentimentInformation3.

  Module MarketSentimentFhlbMessage.

    (** End of day market sentiment aggregate data for Federal Home Loan Bank issues *)
    Record t := {
      message_header : MessageHeader10.t;
      market_sentiment_information : MarketSentimentInformation3.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader10.bounded (message_header record) /\
      MarketSentimentInformation3.bounded (market_sentiment_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader10.encode (message_header record) ++
      MarketSentimentInformation3.encode (market_sentiment_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader10.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match MarketSentimentInformation3.decode bytes with
          | None => None
          | Some (market_sentiment_information_value, bytes) =>
              Some ({| message_header := message_header_value; market_sentiment_information := market_sentiment_information_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 172.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader10.encode_length, !MarketSentimentInformation3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader10.decode_encode by exact bound_0.
      rewrite MarketSentimentInformation3.decode_encode by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader10.eq_dec | apply MarketSentimentInformation3.eq_dec]. Defined.

  End MarketSentimentFhlbMessage.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      trade_identifier : list byte;
      market_center_originator_id : list byte;
      datetime : Datetime11.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime11.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime11.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime11.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module MarketSentimentInformation4.

    (** Market Sentiment Information *)
    Record t := {
      total_number_of_transactions_all_securities : list byte;
      total_securities_traded_all_securities : list byte;
      total_volume_all_securities : list byte;
      total_number_of_transactions_customer_buy : list byte;
      total_securities_traded_customer_buy : list byte;
      total_volume_customer_buy : list byte;
      total_number_of_transactions_customer_sell : list byte;
      total_securities_traded_customer_sell : list byte;
      total_volume_customer_sell : list byte;
      total_number_of_transactions_affiliate_buy : list byte;
      total_securities_traded_affiliate_buy : list byte;
      total_volume_affiliate_buy : list byte;
      total_number_of_transactions_affiliate_sell : list byte;
      total_securities_traded_affiliate_sell : list byte;
      total_volume_affiliate_sell : list byte;
      total_number_of_transactions_inter_dealer : list byte;
      total_securities_traded_inter_dealer : list byte;
      total_volume_inter_dealer : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (total_number_of_transactions_all_securities record) = 6 /\
      Datatypes.length (total_securities_traded_all_securities record) = 6 /\
      Datatypes.length (total_volume_all_securities record) = 13 /\
      Datatypes.length (total_number_of_transactions_customer_buy record) = 6 /\
      Datatypes.length (total_securities_traded_customer_buy record) = 6 /\
      Datatypes.length (total_volume_customer_buy record) = 13 /\
      Datatypes.length (total_number_of_transactions_customer_sell record) = 6 /\
      Datatypes.length (total_securities_traded_customer_sell record) = 6 /\
      Datatypes.length (total_volume_customer_sell record) = 13 /\
      Datatypes.length (total_number_of_transactions_affiliate_buy record) = 6 /\
      Datatypes.length (total_securities_traded_affiliate_buy record) = 6 /\
      Datatypes.length (total_volume_affiliate_buy record) = 13 /\
      Datatypes.length (total_number_of_transactions_affiliate_sell record) = 6 /\
      Datatypes.length (total_securities_traded_affiliate_sell record) = 6 /\
      Datatypes.length (total_volume_affiliate_sell record) = 13 /\
      Datatypes.length (total_number_of_transactions_inter_dealer record) = 6 /\
      Datatypes.length (total_securities_traded_inter_dealer record) = 6 /\
      Datatypes.length (total_volume_inter_dealer record) = 13.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (total_number_of_transactions_all_securities record) ++
      encode_bytes 6 (total_securities_traded_all_securities record) ++
      encode_bytes 13 (total_volume_all_securities record) ++
      encode_bytes 6 (total_number_of_transactions_customer_buy record) ++
      encode_bytes 6 (total_securities_traded_customer_buy record) ++
      encode_bytes 13 (total_volume_customer_buy record) ++
      encode_bytes 6 (total_number_of_transactions_customer_sell record) ++
      encode_bytes 6 (total_securities_traded_customer_sell record) ++
      encode_bytes 13 (total_volume_customer_sell record) ++
      encode_bytes 6 (total_number_of_transactions_affiliate_buy record) ++
      encode_bytes 6 (total_securities_traded_affiliate_buy record) ++
      encode_bytes 13 (total_volume_affiliate_buy record) ++
      encode_bytes 6 (total_number_of_transactions_affiliate_sell record) ++
      encode_bytes 6 (total_securities_traded_affiliate_sell record) ++
      encode_bytes 13 (total_volume_affiliate_sell record) ++
      encode_bytes 6 (total_number_of_transactions_inter_dealer record) ++
      encode_bytes 6 (total_securities_traded_inter_dealer record) ++
      encode_bytes 13 (total_volume_inter_dealer record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (total_number_of_transactions_all_securities_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (total_securities_traded_all_securities_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (total_volume_all_securities_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (total_number_of_transactions_customer_buy_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (total_securities_traded_customer_buy_value, bytes) =>
                          match decode_bytes 13 bytes with
                          | None => None
                          | Some (total_volume_customer_buy_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (total_number_of_transactions_customer_sell_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (total_securities_traded_customer_sell_value, bytes) =>
                                      match decode_bytes 13 bytes with
                                      | None => None
                                      | Some (total_volume_customer_sell_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (total_number_of_transactions_affiliate_buy_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (total_securities_traded_affiliate_buy_value, bytes) =>
                                                  match decode_bytes 13 bytes with
                                                  | None => None
                                                  | Some (total_volume_affiliate_buy_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (total_number_of_transactions_affiliate_sell_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (total_securities_traded_affiliate_sell_value, bytes) =>
                                                              match decode_bytes 13 bytes with
                                                              | None => None
                                                              | Some (total_volume_affiliate_sell_value, bytes) =>
                                                                  match decode_bytes 6 bytes with
                                                                  | None => None
                                                                  | Some (total_number_of_transactions_inter_dealer_value, bytes) =>
                                                                      match decode_bytes 6 bytes with
                                                                      | None => None
                                                                      | Some (total_securities_traded_inter_dealer_value, bytes) =>
                                                                          match decode_bytes 13 bytes with
                                                                          | None => None
                                                                          | Some (total_volume_inter_dealer_value, bytes) =>
                                                                              Some ({| total_number_of_transactions_all_securities := total_number_of_transactions_all_securities_value; total_securities_traded_all_securities := total_securities_traded_all_securities_value; total_volume_all_securities := total_volume_all_securities_value; total_number_of_transactions_customer_buy := total_number_of_transactions_customer_buy_value; total_securities_traded_customer_buy := total_securities_traded_customer_buy_value; total_volume_customer_buy := total_volume_customer_buy_value; total_number_of_transactions_customer_sell := total_number_of_transactions_customer_sell_value; total_securities_traded_customer_sell := total_securities_traded_customer_sell_value; total_volume_customer_sell := total_volume_customer_sell_value; total_number_of_transactions_affiliate_buy := total_number_of_transactions_affiliate_buy_value; total_securities_traded_affiliate_buy := total_securities_traded_affiliate_buy_value; total_volume_affiliate_buy := total_volume_affiliate_buy_value; total_number_of_transactions_affiliate_sell := total_number_of_transactions_affiliate_sell_value; total_securities_traded_affiliate_sell := total_securities_traded_affiliate_sell_value; total_volume_affiliate_sell := total_volume_affiliate_sell_value; total_number_of_transactions_inter_dealer := total_number_of_transactions_inter_dealer_value; total_securities_traded_inter_dealer := total_securities_traded_inter_dealer_value; total_volume_inter_dealer := total_volume_inter_dealer_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 150.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSentimentInformation4.

  Module MarketSentimentFreddieMacMessage.

    (** End of day market sentiment aggregate data for Freddie Mac issues *)
    Record t := {
      message_header : MessageHeader11.t;
      market_sentiment_information : MarketSentimentInformation4.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader11.bounded (message_header record) /\
      MarketSentimentInformation4.bounded (market_sentiment_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader11.encode (message_header record) ++
      MarketSentimentInformation4.encode (market_sentiment_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader11.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match MarketSentimentInformation4.decode bytes with
          | None => None
          | Some (market_sentiment_information_value, bytes) =>
              Some ({| message_header := message_header_value; market_sentiment_information := market_sentiment_information_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 172.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader11.encode_length, !MarketSentimentInformation4.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader11.decode_encode by exact bound_0.
      rewrite MarketSentimentInformation4.decode_encode by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader11.eq_dec | apply MarketSentimentInformation4.eq_dec]. Defined.

  End MarketSentimentFreddieMacMessage.

  Module Datetime12.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime12.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime12.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime12.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module StartOfDayMessage.

    (** Signifies the beginning of each operational cycle *)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End StartOfDayMessage.

  Module Datetime13.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime13.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime13.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime13.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module EndOfDayMessage.

    (** Signifies the end of each operational cycle *)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End EndOfDayMessage.

  Module Datetime14.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime14.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime14.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime14.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module MarketSessionOpenMessage.

    (** Signifies the opening of the market session *)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End MarketSessionOpenMessage.

  Module Datetime15.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime15.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime15.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime15.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module MarketSessionCloseMessage.

    (** Signifies the closing of the market session *)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End MarketSessionCloseMessage.

  Module Datetime16.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime16.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime16.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime16.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module EndOfTradeReportingMessage.

    (** Signifies the end of the trade reporting session *)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End EndOfTradeReportingMessage.

  Module Datetime17.

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
      Datatypes.length (year record) = 4 /\
      Datatypes.length (month record) = 2 /\
      Datatypes.length (day record) = 2 /\
      Datatypes.length (hour record) = 2 /\
      Datatypes.length (minute record) = 2 /\
      Datatypes.length (second record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (year record) ++
      encode_bytes 2 (month record) ++
      encode_bytes 2 (day record) ++
      encode_bytes 2 (hour record) ++
      encode_bytes 2 (minute record) ++
      encode_bytes 2 (second record).

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
                              Some ({| year := year_value; month := month_value; day := day_value; hour := hour_value; minute := minute_value; second := second_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      Datatypes.length (trade_identifier record) = 7 /\
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datetime17.bounded (datetime record).

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_identifier record) ++
      encode_bytes 1 (market_center_originator_id record) ++
      Datetime17.encode (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_originator_id_value, bytes) =>
              match Datetime17.decode bytes with
              | None => None
              | Some (datetime_value, bytes) =>
                  Some ({| trade_identifier := trade_identifier_value; market_center_originator_id := market_center_originator_id_value; datetime := datetime_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  Module EndOfTransmissionsMessage.

    (** Signifies that no further transmissions will be sent for the day *)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End EndOfTransmissionsMessage.

End TraceAtdsV21.
