From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Financial Industry Regulatory Authority Securitized Products Dissemination Service

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

    License: MIT No Attribution
  *)

Module TraceSpdsV21.

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
      factor : list byte;
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
      Datatypes.length (factor record) = 12 /\
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
      encode_bytes 12 (factor record) ++
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
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (factor_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (reporting_party_type_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (contra_party_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (ats_indicator_value, bytes) =>
                                                                      Some ({| quantity_indicator := quantity_indicator_value; quantity := quantity_value; price := price_value; remuneration := remuneration_value; special_price_indicator := special_price_indicator_value; side := side_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; future_use := future_use_value; sale_condition_3 := sale_condition_3_value; sale_condition_4 := sale_condition_4_value; settlement_date := settlement_date_value; factor := factor_value; reporting_party_type := reporting_party_type_value; contra_party_type := contra_party_type_value; ats_indicator := ats_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime.encode_length, !SettlementDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime.eq_dec | apply SettlementDate.eq_dec]. Defined.

  End TradeInformation.

  Module TradeReportMessage.

    (** Used to transmit trade transaction information for Tba, Abs and certain Cmo transactions *)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 142.
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

  Module MbsLabel.

    (** MBS Label *)
    Record t := {
      rdid : list byte;
      sub_product_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (rdid record) = 25 /\
      Datatypes.length (sub_product_type record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 25 (rdid record) ++
      encode_bytes 5 (sub_product_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 25 bytes with
      | None => None
      | Some (rdid_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (sub_product_type_value, bytes) =>
              Some ({| rdid := rdid_value; sub_product_type := sub_product_type_value |}, bytes)
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

  End MbsLabel.

  Module MbsTradeInformation.

    (** MBS Trade Information *)
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
                                                      | Some (reporting_party_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (contra_party_type_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (ats_indicator_value, bytes) =>
                                                                  Some ({| quantity_indicator := quantity_indicator_value; quantity := quantity_value; price := price_value; remuneration := remuneration_value; special_price_indicator := special_price_indicator_value; side := side_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; future_use := future_use_value; sale_condition_3 := sale_condition_3_value; sale_condition_4 := sale_condition_4_value; settlement_date := settlement_date_value; reporting_party_type := reporting_party_type_value; contra_party_type := contra_party_type_value; ats_indicator := ats_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime.encode_length, !SettlementDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime.eq_dec | apply SettlementDate.eq_dec]. Defined.

  End MbsTradeInformation.

  Module MbsTradeReportMessage.

    (** Used to transmit trade transaction information for Mbs transactions *)
    Record t := {
      message_header : MessageHeader.t;
      mbs_label : MbsLabel.t;
      original_dissemination_date : OriginalDisseminationDate.t;
      mbs_trade_information : MbsTradeInformation.t;
      change_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record) /\
      MbsLabel.bounded (mbs_label record) /\
      OriginalDisseminationDate.bounded (original_dissemination_date record) /\
      MbsTradeInformation.bounded (mbs_trade_information record) /\
      Datatypes.length (change_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record) ++
      MbsLabel.encode (mbs_label record) ++
      OriginalDisseminationDate.encode (original_dissemination_date record) ++
      MbsTradeInformation.encode (mbs_trade_information record) ++
      encode_bytes 1 (change_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match MbsLabel.decode bytes with
          | None => None
          | Some (mbs_label_value, bytes) =>
              match OriginalDisseminationDate.decode bytes with
              | None => None
              | Some (original_dissemination_date_value, bytes) =>
                  match MbsTradeInformation.decode bytes with
                  | None => None
                  | Some (mbs_trade_information_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (change_indicator_value, bytes) =>
                          Some ({| message_header := message_header_value; mbs_label := mbs_label_value; original_dissemination_date := original_dissemination_date_value; mbs_trade_information := mbs_trade_information_value; change_indicator := change_indicator_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 120.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader.encode_length, !MbsLabel.encode_length, !OriginalDisseminationDate.encode_length, !MbsTradeInformation.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader.decode_encode by exact bound_0.
      rewrite MbsLabel.decode_encode by exact bound_1.
      rewrite OriginalDisseminationDate.decode_encode by exact bound_2.
      rewrite MbsTradeInformation.decode_encode by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader.eq_dec | apply MbsLabel.eq_dec | apply OriginalDisseminationDate.eq_dec | apply MbsTradeInformation.eq_dec]. Defined.

  End MbsTradeReportMessage.

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
      execution_datetime : ExecutionDatetime.t;
      future_use : list byte;
      sale_condition_3 : list byte;
      sale_condition_4 : list byte;
      settlement_date : SettlementDate.t;
      factor : list byte;
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
      Datatypes.length (factor record) = 12 /\
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
      encode_bytes 12 (factor record) ++
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
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (factor_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (reporting_party_type_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (contra_party_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (ats_indicator_value, bytes) =>
                                                                      Some ({| quantity_indicator := quantity_indicator_value; quantity := quantity_value; price := price_value; remuneration := remuneration_value; special_price_indicator := special_price_indicator_value; side := side_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; future_use := future_use_value; sale_condition_3 := sale_condition_3_value; sale_condition_4 := sale_condition_4_value; settlement_date := settlement_date_value; factor := factor_value; reporting_party_type := reporting_party_type_value; contra_party_type := contra_party_type_value; ats_indicator := ats_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime.encode_length, !SettlementDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime.eq_dec | apply SettlementDate.eq_dec]. Defined.

  End OriginalTradeInformation.

  Module TradeSummaryInformation.

    (** Trade Summary Information *)
    Record t := {
      high_price : list byte;
      low_price : list byte;
      last_sale_price : list byte;
      change_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (high_price record) = 11 /\
      Datatypes.length (low_price record) = 11 /\
      Datatypes.length (last_sale_price record) = 11 /\
      Datatypes.length (change_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (high_price record) ++
      encode_bytes 11 (low_price record) ++
      encode_bytes 11 (last_sale_price record) ++
      encode_bytes 1 (change_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (high_price_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (low_price_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (last_sale_price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (change_indicator_value, bytes) =>
                      Some ({| high_price := high_price_value; low_price := low_price_value; last_sale_price := last_sale_price_value; change_indicator := change_indicator_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
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

  End TradeSummaryInformation.

  Module TradeCancelMessage.

    (** Notifies subscribers that a trade report entered during the past 20 business days has been cancelled *)
    Record t := {
      message_header : MessageHeader.t;
      label : Label.t;
      original_dissemination_date : OriginalDisseminationDate.t;
      original_trade_identifier : list byte;
      report_function : list byte;
      original_trade_information : OriginalTradeInformation.t;
      trade_summary_information : TradeSummaryInformation.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record) /\
      Label.bounded (label record) /\
      OriginalDisseminationDate.bounded (original_dissemination_date record) /\
      Datatypes.length (original_trade_identifier record) = 7 /\
      Datatypes.length (report_function record) = 1 /\
      OriginalTradeInformation.bounded (original_trade_information record) /\
      TradeSummaryInformation.bounded (trade_summary_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record) ++
      Label.encode (label record) ++
      OriginalDisseminationDate.encode (original_dissemination_date record) ++
      encode_bytes 7 (original_trade_identifier record) ++
      encode_bytes 1 (report_function record) ++
      OriginalTradeInformation.encode (original_trade_information record) ++
      TradeSummaryInformation.encode (trade_summary_information record).

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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 183.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader.encode_length, !Label.encode_length, !OriginalDisseminationDate.encode_length, !encode_bytes_length, !OriginalTradeInformation.encode_length, !TradeSummaryInformation.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader.decode_encode by exact bound_0.
      rewrite Label.decode_encode by exact bound_1.
      rewrite OriginalDisseminationDate.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite OriginalTradeInformation.decode_encode by exact bound_5.
      rewrite TradeSummaryInformation.decode_encode by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader.eq_dec | apply Label.eq_dec | apply OriginalDisseminationDate.eq_dec | apply OriginalTradeInformation.eq_dec | apply TradeSummaryInformation.eq_dec]. Defined.

  End TradeCancelMessage.

  Module MbsOriginalTradeInformation.

    (** MBS Original Trade Information *)
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
                                                      | Some (reporting_party_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (contra_party_type_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (ats_indicator_value, bytes) =>
                                                                  Some ({| quantity_indicator := quantity_indicator_value; quantity := quantity_value; price := price_value; remuneration := remuneration_value; special_price_indicator := special_price_indicator_value; side := side_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; future_use := future_use_value; sale_condition_3 := sale_condition_3_value; sale_condition_4 := sale_condition_4_value; settlement_date := settlement_date_value; reporting_party_type := reporting_party_type_value; contra_party_type := contra_party_type_value; ats_indicator := ats_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime.encode_length, !SettlementDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime.eq_dec | apply SettlementDate.eq_dec]. Defined.

  End MbsOriginalTradeInformation.

  Module MbsTradeCancelMessage.

    (** Notifies subscribers that a trade report for an Mbs entered during the past 20 business days has been cancelled *)
    Record t := {
      message_header : MessageHeader.t;
      mbs_label : MbsLabel.t;
      original_dissemination_date : OriginalDisseminationDate.t;
      original_trade_identifier : list byte;
      report_function : list byte;
      mbs_original_trade_information : MbsOriginalTradeInformation.t;
      trade_summary_information : TradeSummaryInformation.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record) /\
      MbsLabel.bounded (mbs_label record) /\
      OriginalDisseminationDate.bounded (original_dissemination_date record) /\
      Datatypes.length (original_trade_identifier record) = 7 /\
      Datatypes.length (report_function record) = 1 /\
      MbsOriginalTradeInformation.bounded (mbs_original_trade_information record) /\
      TradeSummaryInformation.bounded (trade_summary_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record) ++
      MbsLabel.encode (mbs_label record) ++
      OriginalDisseminationDate.encode (original_dissemination_date record) ++
      encode_bytes 7 (original_trade_identifier record) ++
      encode_bytes 1 (report_function record) ++
      MbsOriginalTradeInformation.encode (mbs_original_trade_information record) ++
      TradeSummaryInformation.encode (trade_summary_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match MbsLabel.decode bytes with
          | None => None
          | Some (mbs_label_value, bytes) =>
              match OriginalDisseminationDate.decode bytes with
              | None => None
              | Some (original_dissemination_date_value, bytes) =>
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (original_trade_identifier_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (report_function_value, bytes) =>
                          match MbsOriginalTradeInformation.decode bytes with
                          | None => None
                          | Some (mbs_original_trade_information_value, bytes) =>
                              match TradeSummaryInformation.decode bytes with
                              | None => None
                              | Some (trade_summary_information_value, bytes) =>
                                  Some ({| message_header := message_header_value; mbs_label := mbs_label_value; original_dissemination_date := original_dissemination_date_value; original_trade_identifier := original_trade_identifier_value; report_function := report_function_value; mbs_original_trade_information := mbs_original_trade_information_value; trade_summary_information := trade_summary_information_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 161.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader.encode_length, !MbsLabel.encode_length, !OriginalDisseminationDate.encode_length, !encode_bytes_length, !MbsOriginalTradeInformation.encode_length, !TradeSummaryInformation.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader.decode_encode by exact bound_0.
      rewrite MbsLabel.decode_encode by exact bound_1.
      rewrite OriginalDisseminationDate.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite MbsOriginalTradeInformation.decode_encode by exact bound_5.
      rewrite TradeSummaryInformation.decode_encode by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader.eq_dec | apply MbsLabel.eq_dec | apply OriginalDisseminationDate.eq_dec | apply MbsOriginalTradeInformation.eq_dec | apply TradeSummaryInformation.eq_dec]. Defined.

  End MbsTradeCancelMessage.

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
      execution_datetime : ExecutionDatetime.t;
      future_use : list byte;
      sale_condition_3 : list byte;
      sale_condition_4 : list byte;
      settlement_date : SettlementDate.t;
      factor : list byte;
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
      Datatypes.length (factor record) = 12 /\
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
      encode_bytes 12 (factor record) ++
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
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (factor_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (reporting_party_type_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (contra_party_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (ats_indicator_value, bytes) =>
                                                                      Some ({| quantity_indicator := quantity_indicator_value; quantity := quantity_value; price := price_value; remuneration := remuneration_value; special_price_indicator := special_price_indicator_value; side := side_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; future_use := future_use_value; sale_condition_3 := sale_condition_3_value; sale_condition_4 := sale_condition_4_value; settlement_date := settlement_date_value; factor := factor_value; reporting_party_type := reporting_party_type_value; contra_party_type := contra_party_type_value; ats_indicator := ats_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime.encode_length, !SettlementDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime.eq_dec | apply SettlementDate.eq_dec]. Defined.

  End CorrectionTradeInformation.

  Module TradeCorrectionMessage.

    (** Notifies subscribers that a trade report entered during the past 20 business days has been corrected *)
    Record t := {
      message_header : MessageHeader.t;
      label : Label.t;
      original_dissemination_date : OriginalDisseminationDate.t;
      original_trade_identifier : list byte;
      report_function : list byte;
      original_trade_information : OriginalTradeInformation.t;
      correction_trade_information : CorrectionTradeInformation.t;
      trade_summary_information : TradeSummaryInformation.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record) /\
      Label.bounded (label record) /\
      OriginalDisseminationDate.bounded (original_dissemination_date record) /\
      Datatypes.length (original_trade_identifier record) = 7 /\
      Datatypes.length (report_function record) = 1 /\
      OriginalTradeInformation.bounded (original_trade_information record) /\
      CorrectionTradeInformation.bounded (correction_trade_information record) /\
      TradeSummaryInformation.bounded (trade_summary_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record) ++
      Label.encode (label record) ++
      OriginalDisseminationDate.encode (original_dissemination_date record) ++
      encode_bytes 7 (original_trade_identifier record) ++
      encode_bytes 1 (report_function record) ++
      OriginalTradeInformation.encode (original_trade_information record) ++
      CorrectionTradeInformation.encode (correction_trade_information record) ++
      TradeSummaryInformation.encode (trade_summary_information record).

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
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (original_trade_identifier_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (report_function_value, bytes) =>
                          match OriginalTradeInformation.decode bytes with
                          | None => None
                          | Some (original_trade_information_value, bytes) =>
                              match CorrectionTradeInformation.decode bytes with
                              | None => None
                              | Some (correction_trade_information_value, bytes) =>
                                  match TradeSummaryInformation.decode bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 254.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader.encode_length, !Label.encode_length, !OriginalDisseminationDate.encode_length, !encode_bytes_length, !OriginalTradeInformation.encode_length, !CorrectionTradeInformation.encode_length, !TradeSummaryInformation.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader.decode_encode by exact bound_0.
      rewrite Label.decode_encode by exact bound_1.
      rewrite OriginalDisseminationDate.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite OriginalTradeInformation.decode_encode by exact bound_5.
      rewrite CorrectionTradeInformation.decode_encode by exact bound_6.
      rewrite TradeSummaryInformation.decode_encode by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader.eq_dec | apply Label.eq_dec | apply OriginalDisseminationDate.eq_dec | apply OriginalTradeInformation.eq_dec | apply CorrectionTradeInformation.eq_dec | apply TradeSummaryInformation.eq_dec]. Defined.

  End TradeCorrectionMessage.

  Module MbsCorrectionTradeInformation.

    (** MBS Correction Trade Information *)
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
                                                      | Some (reporting_party_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (contra_party_type_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (ats_indicator_value, bytes) =>
                                                                  Some ({| quantity_indicator := quantity_indicator_value; quantity := quantity_value; price := price_value; remuneration := remuneration_value; special_price_indicator := special_price_indicator_value; side := side_value; as_of_indicator := as_of_indicator_value; execution_datetime := execution_datetime_value; future_use := future_use_value; sale_condition_3 := sale_condition_3_value; sale_condition_4 := sale_condition_4_value; settlement_date := settlement_date_value; reporting_party_type := reporting_party_type_value; contra_party_type := contra_party_type_value; ats_indicator := ats_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecutionDatetime.encode_length, !SettlementDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutionDatetime.eq_dec | apply SettlementDate.eq_dec]. Defined.

  End MbsCorrectionTradeInformation.

  Module MbsTradeCorrectionMessage.

    (** Notifies subscribers that a trade report for an Mbs entered during the past 20 business days has been corrected *)
    Record t := {
      message_header : MessageHeader.t;
      mbs_label : MbsLabel.t;
      original_dissemination_date : OriginalDisseminationDate.t;
      original_trade_identifier : list byte;
      report_function : list byte;
      mbs_original_trade_information : MbsOriginalTradeInformation.t;
      mbs_correction_trade_information : MbsCorrectionTradeInformation.t;
      trade_summary_information : TradeSummaryInformation.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record) /\
      MbsLabel.bounded (mbs_label record) /\
      OriginalDisseminationDate.bounded (original_dissemination_date record) /\
      Datatypes.length (original_trade_identifier record) = 7 /\
      Datatypes.length (report_function record) = 1 /\
      MbsOriginalTradeInformation.bounded (mbs_original_trade_information record) /\
      MbsCorrectionTradeInformation.bounded (mbs_correction_trade_information record) /\
      TradeSummaryInformation.bounded (trade_summary_information record).

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record) ++
      MbsLabel.encode (mbs_label record) ++
      OriginalDisseminationDate.encode (original_dissemination_date record) ++
      encode_bytes 7 (original_trade_identifier record) ++
      encode_bytes 1 (report_function record) ++
      MbsOriginalTradeInformation.encode (mbs_original_trade_information record) ++
      MbsCorrectionTradeInformation.encode (mbs_correction_trade_information record) ++
      TradeSummaryInformation.encode (trade_summary_information record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match MbsLabel.decode bytes with
          | None => None
          | Some (mbs_label_value, bytes) =>
              match OriginalDisseminationDate.decode bytes with
              | None => None
              | Some (original_dissemination_date_value, bytes) =>
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (original_trade_identifier_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (report_function_value, bytes) =>
                          match MbsOriginalTradeInformation.decode bytes with
                          | None => None
                          | Some (mbs_original_trade_information_value, bytes) =>
                              match MbsCorrectionTradeInformation.decode bytes with
                              | None => None
                              | Some (mbs_correction_trade_information_value, bytes) =>
                                  match TradeSummaryInformation.decode bytes with
                                  | None => None
                                  | Some (trade_summary_information_value, bytes) =>
                                      Some ({| message_header := message_header_value; mbs_label := mbs_label_value; original_dissemination_date := original_dissemination_date_value; original_trade_identifier := original_trade_identifier_value; report_function := report_function_value; mbs_original_trade_information := mbs_original_trade_information_value; mbs_correction_trade_information := mbs_correction_trade_information_value; trade_summary_information := trade_summary_information_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 220.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader.encode_length, !MbsLabel.encode_length, !OriginalDisseminationDate.encode_length, !encode_bytes_length, !MbsOriginalTradeInformation.encode_length, !MbsCorrectionTradeInformation.encode_length, !TradeSummaryInformation.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader.decode_encode by exact bound_0.
      rewrite MbsLabel.decode_encode by exact bound_1.
      rewrite OriginalDisseminationDate.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite MbsOriginalTradeInformation.decode_encode by exact bound_5.
      rewrite MbsCorrectionTradeInformation.decode_encode by exact bound_6.
      rewrite TradeSummaryInformation.decode_encode by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader.eq_dec | apply MbsLabel.eq_dec | apply OriginalDisseminationDate.eq_dec | apply MbsOriginalTradeInformation.eq_dec | apply MbsCorrectionTradeInformation.eq_dec | apply TradeSummaryInformation.eq_dec]. Defined.

  End MbsTradeCorrectionMessage.

  Module DailyTradeSummaryMessage.

    (** Price summary disseminated for each security that traded during the normal trading hours *)
    Record t := {
      message_header : MessageHeader.t;
      label : Label.t;
      daily_high_price : list byte;
      daily_low_price : list byte;
      daily_close_price : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record) /\
      Label.bounded (label record) /\
      Datatypes.length (daily_high_price record) = 11 /\
      Datatypes.length (daily_low_price record) = 11 /\
      Datatypes.length (daily_close_price record) = 11.

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record) ++
      Label.encode (label record) ++
      encode_bytes 11 (daily_high_price record) ++
      encode_bytes 11 (daily_low_price record) ++
      encode_bytes 11 (daily_close_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match Label.decode bytes with
          | None => None
          | Some (label_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (daily_high_price_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (daily_low_price_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (daily_close_price_value, bytes) =>
                          Some ({| message_header := message_header_value; label := label_value; daily_high_price := daily_high_price_value; daily_low_price := daily_low_price_value; daily_close_price := daily_close_price_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 95.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader.encode_length, !Label.encode_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader.eq_dec | apply Label.eq_dec]. Defined.

  End DailyTradeSummaryMessage.

  Module MbsDailyTradeSummaryMessage.

    (** Price summary disseminated for each Mbs that traded during the normal trading hours *)
    Record t := {
      message_header : MessageHeader.t;
      mbs_label : MbsLabel.t;
      daily_high_price : list byte;
      daily_low_price : list byte;
      daily_close_price : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record) /\
      MbsLabel.bounded (mbs_label record) /\
      Datatypes.length (daily_high_price record) = 11 /\
      Datatypes.length (daily_low_price record) = 11 /\
      Datatypes.length (daily_close_price record) = 11.

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record) ++
      MbsLabel.encode (mbs_label record) ++
      encode_bytes 11 (daily_high_price record) ++
      encode_bytes 11 (daily_low_price record) ++
      encode_bytes 11 (daily_close_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match MbsLabel.decode bytes with
          | None => None
          | Some (mbs_label_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (daily_high_price_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (daily_low_price_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (daily_close_price_value, bytes) =>
                          Some ({| message_header := message_header_value; mbs_label := mbs_label_value; daily_high_price := daily_high_price_value; daily_low_price := daily_low_price_value; daily_close_price := daily_close_price_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 85.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageHeader.encode_length, !MbsLabel.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader.decode_encode by exact bound_0.
      rewrite MbsLabel.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader.eq_dec | apply MbsLabel.eq_dec]. Defined.

  End MbsDailyTradeSummaryMessage.

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

    (** Disseminated when a trading halt is instituted or removed for a security *)
    Record t := {
      message_header : MessageHeader.t;
      label : Label.t;
      issuer : list byte;
      action : list byte;
      action_datetime : ActionDatetime.t;
      halt_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record) /\
      Label.bounded (label record) /\
      Datatypes.length (issuer record) = 30 /\
      Datatypes.length (action record) = 1 /\
      ActionDatetime.bounded (action_datetime record) /\
      Datatypes.length (halt_reason record) = 4.

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record) ++
      Label.encode (label record) ++
      encode_bytes 30 (issuer record) ++
      encode_bytes 1 (action record) ++
      ActionDatetime.encode (action_datetime record) ++
      encode_bytes 4 (halt_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          match Label.decode bytes with
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
      rewrite !length_app, !MessageHeader.encode_length, !Label.encode_length, !encode_bytes_length, !ActionDatetime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageHeader.decode_encode by exact bound_0.
      rewrite Label.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite ActionDatetime.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageHeader.eq_dec | apply Label.eq_dec | apply ActionDatetime.eq_dec]. Defined.

  End TradingHaltMessage.

  Module StartOfDayMessage.

    (** Signifies the beginning of Finra's daily operational cycle *)
    Record t := {
      message_header : MessageHeader.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader.eq_dec]. Defined.

  End StartOfDayMessage.

  Module EndOfDayMessage.

    (** Signals the end of activity for the operational cycle *)
    Record t := {
      message_header : MessageHeader.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader.eq_dec]. Defined.

  End EndOfDayMessage.

  Module MarketSessionOpenMessage.

    (** Signifies the opening of the market for the session indicated in the message header *)
    Record t := {
      message_header : MessageHeader.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader.eq_dec]. Defined.

  End MarketSessionOpenMessage.

  Module MarketSessionCloseMessage.

    (** Signals the closing of the market for the session indicated in the message header *)
    Record t := {
      message_header : MessageHeader.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader.eq_dec]. Defined.

  End MarketSessionCloseMessage.

  Module EndOfTradeReportingMessage.

    (** Signals that no further trade reports or corrections will be sent for that market session *)
    Record t := {
      message_header : MessageHeader.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader.eq_dec]. Defined.

  End EndOfTradeReportingMessage.

  Module EndOfTransmissionsMessage.

    (** Signals that there will be no further transmissions of data *)
    Record t := {
      message_header : MessageHeader.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageHeader.bounded (message_header record).

    Definition encode (record : t) : list byte :=
      MessageHeader.encode (message_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageHeader.decode bytes with
      | None => None
      | Some (message_header_value, bytes) =>
          Some ({| message_header := message_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !MessageHeader.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageHeader.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageHeader.eq_dec]. Defined.

  End EndOfTransmissionsMessage.

End TraceSpdsV21.
