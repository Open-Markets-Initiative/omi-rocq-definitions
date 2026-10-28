From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Last Sale

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
      - the dispatch that chooses a message by its type
      - a run counted by a field
  *)

Module NsmEquitiesLastSaleV102010.

  Module PacketHeader.

    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End MessageHeader.

  Module SystemEventMessage.

    (** System Event Messages is used to signal key market or data feed control events. *)
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

  Module SaleConditionModifier.

    (** Sale Condition Modifier *)
    Record t := {
      settlement_type : list byte;
      trade_through_exemption : list byte;
      extended_hours_or_sold_code : list byte;
      special_sale_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exemption record) = 1 /\
      Datatypes.length (extended_hours_or_sold_code record) = 1 /\
      Datatypes.length (special_sale_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exemption record) ++
      encode_bytes 1 (extended_hours_or_sold_code record) ++
      encode_bytes 1 (special_sale_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exemption_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sold_code_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (special_sale_condition_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exemption := trade_through_exemption_value; extended_hours_or_sold_code := extended_hours_or_sold_code_value; special_sale_condition := special_sale_condition_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SaleConditionModifier.

  Module TradeReportMessage.

    (** The following message is used to relay NASDAQ execution system and TRF trade transactions that are reported for the current business day. Please note that NASDAQ only reports one-side of a trade execution on the NASDAQ Last Sale (NLS) feed and other data feed products. *)
    Record t := {
      market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      trade_control_number : list byte;
      trade_price : list byte;
      trade_size : list byte;
      sale_condition_modifier : SaleConditionModifier.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 6 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (trade_control_number record) = 10 /\
      Datatypes.length (trade_price record) = 10 /\
      Datatypes.length (trade_size record) = 9 /\
      SaleConditionModifier.bounded (sale_condition_modifier record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_identifier record) ++
      encode_bytes 6 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (trade_control_number record) ++
      encode_bytes 10 (trade_price record) ++
      encode_bytes 9 (trade_size record) ++
      SaleConditionModifier.encode (sale_condition_modifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_identifier_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (trade_control_number_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (trade_price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (trade_size_value, bytes) =>
                              match SaleConditionModifier.decode bytes with
                              | None => None
                              | Some (sale_condition_modifier_value, bytes) =>
                                  Some ({| market_center_identifier := market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; trade_control_number := trade_control_number_value; trade_price := trade_price_value; trade_size := trade_size_value; sale_condition_modifier := sale_condition_modifier_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !SaleConditionModifier.encode_length. reflexivity.
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
      rewrite SaleConditionModifier.decode_encode by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditionModifier.eq_dec]. Defined.

  End TradeReportMessage.

  Module OriginalSaleConditionModifier.

    (** Original Sale Condition Modifier *)
    Record t := {
      original_settlement_type : list byte;
      original_trade_through_exemption : list byte;
      original_extended_hours_or_sold_code : list byte;
      original_special_sale_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (original_settlement_type record) = 1 /\
      Datatypes.length (original_trade_through_exemption record) = 1 /\
      Datatypes.length (original_extended_hours_or_sold_code record) = 1 /\
      Datatypes.length (original_special_sale_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (original_settlement_type record) ++
      encode_bytes 1 (original_trade_through_exemption record) ++
      encode_bytes 1 (original_extended_hours_or_sold_code record) ++
      encode_bytes 1 (original_special_sale_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (original_settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (original_trade_through_exemption_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (original_extended_hours_or_sold_code_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (original_special_sale_condition_value, bytes) =>
                      Some ({| original_settlement_type := original_settlement_type_value; original_trade_through_exemption := original_trade_through_exemption_value; original_extended_hours_or_sold_code := original_extended_hours_or_sold_code_value; original_special_sale_condition := original_special_sale_condition_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End OriginalSaleConditionModifier.

  Module TradeCancelErrorMessage.

    (** The following message is used in the event that a NASDAQ or TRF trade transaction is cancelled on the same business day that it is reported. *)
    Record t := {
      market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      original_trade_control_number : list byte;
      original_trade_price : list byte;
      original_trade_size : list byte;
      original_sale_condition_modifier : OriginalSaleConditionModifier.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 6 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (original_trade_control_number record) = 10 /\
      Datatypes.length (original_trade_price record) = 10 /\
      Datatypes.length (original_trade_size record) = 9 /\
      OriginalSaleConditionModifier.bounded (original_sale_condition_modifier record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_identifier record) ++
      encode_bytes 6 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (original_trade_control_number record) ++
      encode_bytes 10 (original_trade_price record) ++
      encode_bytes 9 (original_trade_size record) ++
      OriginalSaleConditionModifier.encode (original_sale_condition_modifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_identifier_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (original_trade_control_number_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (original_trade_price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (original_trade_size_value, bytes) =>
                              match OriginalSaleConditionModifier.decode bytes with
                              | None => None
                              | Some (original_sale_condition_modifier_value, bytes) =>
                                  Some ({| market_center_identifier := market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; original_trade_control_number := original_trade_control_number_value; original_trade_price := original_trade_price_value; original_trade_size := original_trade_size_value; original_sale_condition_modifier := original_sale_condition_modifier_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !OriginalSaleConditionModifier.encode_length. reflexivity.
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
      rewrite OriginalSaleConditionModifier.decode_encode by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OriginalSaleConditionModifier.eq_dec]. Defined.

  End TradeCancelErrorMessage.

  Module OriginalSaleConditionModifier2.

    (** Original Sale Condition Modifier *)
    Record t := {
      original_settlement_type : list byte;
      original_trade_through_exemption : list byte;
      original_extended_hours_or_sold_code : list byte;
      original_special_sale_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (original_settlement_type record) = 1 /\
      Datatypes.length (original_trade_through_exemption record) = 1 /\
      Datatypes.length (original_extended_hours_or_sold_code record) = 1 /\
      Datatypes.length (original_special_sale_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (original_settlement_type record) ++
      encode_bytes 1 (original_trade_through_exemption record) ++
      encode_bytes 1 (original_extended_hours_or_sold_code record) ++
      encode_bytes 1 (original_special_sale_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (original_settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (original_trade_through_exemption_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (original_extended_hours_or_sold_code_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (original_special_sale_condition_value, bytes) =>
                      Some ({| original_settlement_type := original_settlement_type_value; original_trade_through_exemption := original_trade_through_exemption_value; original_extended_hours_or_sold_code := original_extended_hours_or_sold_code_value; original_special_sale_condition := original_special_sale_condition_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End OriginalSaleConditionModifier2.

  Module CorrectedSaleConditionModifier.

    (** Corrected Sale Condition Modifier *)
    Record t := {
      corrected_settlement_type : list byte;
      corrected_trade_through_exemption : list byte;
      corrected_extended_hours_or_sold_code : list byte;
      corrected_special_sale_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (corrected_settlement_type record) = 1 /\
      Datatypes.length (corrected_trade_through_exemption record) = 1 /\
      Datatypes.length (corrected_extended_hours_or_sold_code record) = 1 /\
      Datatypes.length (corrected_special_sale_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (corrected_settlement_type record) ++
      encode_bytes 1 (corrected_trade_through_exemption record) ++
      encode_bytes 1 (corrected_extended_hours_or_sold_code record) ++
      encode_bytes 1 (corrected_special_sale_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (corrected_settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (corrected_trade_through_exemption_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (corrected_extended_hours_or_sold_code_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (corrected_special_sale_condition_value, bytes) =>
                      Some ({| corrected_settlement_type := corrected_settlement_type_value; corrected_trade_through_exemption := corrected_trade_through_exemption_value; corrected_extended_hours_or_sold_code := corrected_extended_hours_or_sold_code_value; corrected_special_sale_condition := corrected_special_sale_condition_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End CorrectedSaleConditionModifier.

  Module TradeCorrectionMessage.

    (** The following message is used in the event that a TRF trade transaction is corrected on the same business day that it is reported. *)
    Record t := {
      market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      original_trade_control_number : list byte;
      original_trade_price : list byte;
      original_trade_size : list byte;
      original_sale_condition_modifier : OriginalSaleConditionModifier2.t;
      corrected_trade_control_number : list byte;
      corrected_trade_price : list byte;
      corrected_trade_size : list byte;
      corrected_sale_condition_modifier : CorrectedSaleConditionModifier.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 6 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (original_trade_control_number record) = 10 /\
      Datatypes.length (original_trade_price record) = 10 /\
      Datatypes.length (original_trade_size record) = 9 /\
      OriginalSaleConditionModifier2.bounded (original_sale_condition_modifier record) /\
      Datatypes.length (corrected_trade_control_number record) = 10 /\
      Datatypes.length (corrected_trade_price record) = 10 /\
      Datatypes.length (corrected_trade_size record) = 9 /\
      CorrectedSaleConditionModifier.bounded (corrected_sale_condition_modifier record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_identifier record) ++
      encode_bytes 6 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (original_trade_control_number record) ++
      encode_bytes 10 (original_trade_price record) ++
      encode_bytes 9 (original_trade_size record) ++
      OriginalSaleConditionModifier2.encode (original_sale_condition_modifier record) ++
      encode_bytes 10 (corrected_trade_control_number record) ++
      encode_bytes 10 (corrected_trade_price record) ++
      encode_bytes 9 (corrected_trade_size record) ++
      CorrectedSaleConditionModifier.encode (corrected_sale_condition_modifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_identifier_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (original_trade_control_number_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (original_trade_price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (original_trade_size_value, bytes) =>
                              match OriginalSaleConditionModifier2.decode bytes with
                              | None => None
                              | Some (original_sale_condition_modifier_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (corrected_trade_control_number_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (corrected_trade_price_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (corrected_trade_size_value, bytes) =>
                                              match CorrectedSaleConditionModifier.decode bytes with
                                              | None => None
                                              | Some (corrected_sale_condition_modifier_value, bytes) =>
                                                  Some ({| market_center_identifier := market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; original_trade_control_number := original_trade_control_number_value; original_trade_price := original_trade_price_value; original_trade_size := original_trade_size_value; original_sale_condition_modifier := original_sale_condition_modifier_value; corrected_trade_control_number := corrected_trade_control_number_value; corrected_trade_price := corrected_trade_price_value; corrected_trade_size := corrected_trade_size_value; corrected_sale_condition_modifier := corrected_sale_condition_modifier_value |}, bytes)
                                              end
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
      rewrite !length_app, !encode_bytes_length, !OriginalSaleConditionModifier2.encode_length, !CorrectedSaleConditionModifier.encode_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite OriginalSaleConditionModifier2.decode_encode by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite CorrectedSaleConditionModifier.decode_encode by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OriginalSaleConditionModifier2.eq_dec | apply CorrectedSaleConditionModifier.eq_dec]. Defined.

  End TradeCorrectionMessage.

  Module StockTradingActionMessage.

    (** NASDAQ uses this administrative message to indicate the current trading status of a security to the trading community. *)
    Record t := {
      issue_symbol : list byte;
      security_class : list byte;
      current_trading_state : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_symbol record) = 6 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (current_trading_state record) = 1 /\
      Datatypes.length (reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 1 (current_trading_state record) ++
      encode_bytes 4 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (issue_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (security_class_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (current_trading_state_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (reason_value, bytes) =>
                      Some ({| issue_symbol := issue_symbol_value; security_class := security_class_value; current_trading_state := current_trading_state_value; reason := reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End StockTradingActionMessage.

  Module StockDirectoryMessage.

    (** At the start of each trading day, NASDAQ disseminates stock directory messages for all active symbols in the NASDAQ system. *)
    Record t := {
      issue_symbol : list byte;
      market_category : list byte;
      financial_status_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_symbol record) = 6 /\
      Datatypes.length (market_category record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (issue_symbol record) ++
      encode_bytes 1 (market_category record) ++
      encode_bytes 1 (financial_status_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (issue_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_category_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (financial_status_indicator_value, bytes) =>
                  Some ({| issue_symbol := issue_symbol_value; market_category := market_category_value; financial_status_indicator := financial_status_indicator_value |}, bytes)
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

  End StockDirectoryMessage.

End NsmEquitiesLastSaleV102010.
