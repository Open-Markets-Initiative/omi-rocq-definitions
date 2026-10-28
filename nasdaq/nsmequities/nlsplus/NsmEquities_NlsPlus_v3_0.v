From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Last Sale Plus

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

Module NsmEquitiesNlsPlusV30.

  Module PacketHeader.

    (** Itch Mold Udp 64 Packet Header *)
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

    Record t := {
      message_length : N;
      tracking_number : N;
      timestamp : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (message_type_value, bytes) =>
                      Some ({| message_length := message_length_value; tracking_number := tracking_number_value; timestamp := timestamp_value; message_type := message_type_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
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

    (** Sale condition modifier, consisting of four levels *)
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

    (** Relays Nasdaq execution system and Trf trade transactions reported for the current business day. Nasdaq reports only one side of a trade execution on the Nls Plus feed. *)
    Record t := {
      originating_market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      trade_control_number : list byte;
      trade_price : N;
      trade_size : N;
      sale_condition_modifier : SaleConditionModifier.t;
      consolidated_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (trade_control_number record) = 10 /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (trade_size record < 256 ^ N.of_nat 4)%N /\
      SaleConditionModifier.bounded (sale_condition_modifier record) /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (trade_control_number record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 4 (trade_size record) ++
      SaleConditionModifier.encode (sale_condition_modifier record) ++
      encode_uint 8 (consolidated_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (originating_market_center_identifier_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (trade_control_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_size_value, bytes) =>
                              match SaleConditionModifier.decode bytes with
                              | None => None
                              | Some (sale_condition_modifier_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (consolidated_volume_value, bytes) =>
                                      Some ({| originating_market_center_identifier := originating_market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; trade_control_number := trade_control_number_value; trade_price := trade_price_value; trade_size := trade_size_value; sale_condition_modifier := sale_condition_modifier_value; consolidated_volume := consolidated_volume_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !SaleConditionModifier.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite SaleConditionModifier.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditionModifier.eq_dec]. Defined.

  End TradeReportMessage.

  Module SaleConditionModifier2.

    (** Sale condition modifier, consisting of four levels *)
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

  End SaleConditionModifier2.

  Module LongFormTradeReportMessage.

    (** Trade Report carrying an eight byte trade price, used when the price breaches the maximum value the four byte form can carry. *)
    Record t := {
      originating_market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      trade_control_number : list byte;
      trade_price_long : N;
      trade_size : N;
      sale_condition_modifier : SaleConditionModifier2.t;
      consolidated_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (trade_control_number record) = 10 /\
      (trade_price_long record < 256 ^ N.of_nat 8)%N /\
      (trade_size record < 256 ^ N.of_nat 4)%N /\
      SaleConditionModifier2.bounded (sale_condition_modifier record) /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (trade_control_number record) ++
      encode_uint 8 (trade_price_long record) ++
      encode_uint 4 (trade_size record) ++
      SaleConditionModifier2.encode (sale_condition_modifier record) ++
      encode_uint 8 (consolidated_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (originating_market_center_identifier_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (trade_control_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_price_long_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_size_value, bytes) =>
                              match SaleConditionModifier2.decode bytes with
                              | None => None
                              | Some (sale_condition_modifier_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (consolidated_volume_value, bytes) =>
                                      Some ({| originating_market_center_identifier := originating_market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; trade_control_number := trade_control_number_value; trade_price_long := trade_price_long_value; trade_size := trade_size_value; sale_condition_modifier := sale_condition_modifier_value; consolidated_volume := consolidated_volume_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !SaleConditionModifier2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite SaleConditionModifier2.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditionModifier2.eq_dec]. Defined.

  End LongFormTradeReportMessage.

  Module SaleConditionModifier3.

    (** Sale condition modifier, consisting of four levels *)
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

  End SaleConditionModifier3.

  Module NextSharesTradeReportMessage.

    (** Relays trade transactions for NextShares exchange traded managed funds, reported as a proxy price with the Nav offset to apply to it. *)
    Record t := {
      originating_market_center_identifier : list byte;
      next_shares_symbol : list byte;
      security_class : list byte;
      trade_control_number : list byte;
      proxy_price : N;
      trade_size : N;
      nav_offset_amount : N;
      sale_condition_modifier : SaleConditionModifier3.t;
      consolidated_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (next_shares_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (trade_control_number record) = 10 /\
      (proxy_price record < 256 ^ N.of_nat 4)%N /\
      (trade_size record < 256 ^ N.of_nat 4)%N /\
      (nav_offset_amount record < 256 ^ N.of_nat 4)%N /\
      SaleConditionModifier3.bounded (sale_condition_modifier record) /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 8 (next_shares_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (trade_control_number record) ++
      encode_uint 4 (proxy_price record) ++
      encode_uint 4 (trade_size record) ++
      encode_uint 4 (nav_offset_amount record) ++
      SaleConditionModifier3.encode (sale_condition_modifier record) ++
      encode_uint 8 (consolidated_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (originating_market_center_identifier_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (next_shares_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (trade_control_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (proxy_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_size_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (nav_offset_amount_value, bytes) =>
                                  match SaleConditionModifier3.decode bytes with
                                  | None => None
                                  | Some (sale_condition_modifier_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (consolidated_volume_value, bytes) =>
                                          Some ({| originating_market_center_identifier := originating_market_center_identifier_value; next_shares_symbol := next_shares_symbol_value; security_class := security_class_value; trade_control_number := trade_control_number_value; proxy_price := proxy_price_value; trade_size := trade_size_value; nav_offset_amount := nav_offset_amount_value; sale_condition_modifier := sale_condition_modifier_value; consolidated_volume := consolidated_volume_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !SaleConditionModifier3.encode_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite SaleConditionModifier3.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditionModifier3.eq_dec]. Defined.

  End NextSharesTradeReportMessage.

  Module OriginalSaleConditionModifier.

    (** The sale condition modifier reported on the original trade transaction *)
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

    (** Indicates that a previously reported trade transaction has been cancelled or was reported in error. *)
    Record t := {
      originating_market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      original_trade_control_number : list byte;
      original_trade_price : N;
      original_trade_size : N;
      original_sale_condition_modifier : OriginalSaleConditionModifier.t;
      consolidated_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (original_trade_control_number record) = 10 /\
      (original_trade_price record < 256 ^ N.of_nat 4)%N /\
      (original_trade_size record < 256 ^ N.of_nat 4)%N /\
      OriginalSaleConditionModifier.bounded (original_sale_condition_modifier record) /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (original_trade_control_number record) ++
      encode_uint 4 (original_trade_price record) ++
      encode_uint 4 (original_trade_size record) ++
      OriginalSaleConditionModifier.encode (original_sale_condition_modifier record) ++
      encode_uint 8 (consolidated_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (originating_market_center_identifier_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (original_trade_control_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (original_trade_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (original_trade_size_value, bytes) =>
                              match OriginalSaleConditionModifier.decode bytes with
                              | None => None
                              | Some (original_sale_condition_modifier_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (consolidated_volume_value, bytes) =>
                                      Some ({| originating_market_center_identifier := originating_market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; original_trade_control_number := original_trade_control_number_value; original_trade_price := original_trade_price_value; original_trade_size := original_trade_size_value; original_sale_condition_modifier := original_sale_condition_modifier_value; consolidated_volume := consolidated_volume_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !OriginalSaleConditionModifier.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite OriginalSaleConditionModifier.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OriginalSaleConditionModifier.eq_dec]. Defined.

  End TradeCancelErrorMessage.

  Module OriginalSaleConditionModifier2.

    (** The sale condition modifier reported on the original trade transaction *)
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

  Module LongFormTradeCancelErrorMessage.

    (** Trade Cancel/Error carrying an eight byte original trade price. *)
    Record t := {
      originating_market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      original_trade_control_number : list byte;
      original_trade_price_long : N;
      original_trade_size : N;
      original_sale_condition_modifier : OriginalSaleConditionModifier2.t;
      consolidated_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (original_trade_control_number record) = 10 /\
      (original_trade_price_long record < 256 ^ N.of_nat 8)%N /\
      (original_trade_size record < 256 ^ N.of_nat 4)%N /\
      OriginalSaleConditionModifier2.bounded (original_sale_condition_modifier record) /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (original_trade_control_number record) ++
      encode_uint 8 (original_trade_price_long record) ++
      encode_uint 4 (original_trade_size record) ++
      OriginalSaleConditionModifier2.encode (original_sale_condition_modifier record) ++
      encode_uint 8 (consolidated_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (originating_market_center_identifier_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (original_trade_control_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_trade_price_long_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (original_trade_size_value, bytes) =>
                              match OriginalSaleConditionModifier2.decode bytes with
                              | None => None
                              | Some (original_sale_condition_modifier_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (consolidated_volume_value, bytes) =>
                                      Some ({| originating_market_center_identifier := originating_market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; original_trade_control_number := original_trade_control_number_value; original_trade_price_long := original_trade_price_long_value; original_trade_size := original_trade_size_value; original_sale_condition_modifier := original_sale_condition_modifier_value; consolidated_volume := consolidated_volume_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !OriginalSaleConditionModifier2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite OriginalSaleConditionModifier2.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OriginalSaleConditionModifier2.eq_dec]. Defined.

  End LongFormTradeCancelErrorMessage.

  Module OriginalSaleConditionModifier3.

    (** The sale condition modifier reported on the original trade transaction *)
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

  End OriginalSaleConditionModifier3.

  Module NextSharesTradeCancelErrorMessage.

    (** Indicates that a previously reported NextShares trade transaction has been cancelled or was reported in error. *)
    Record t := {
      market_center : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      original_trade_control_number : list byte;
      original_proxy_price : N;
      original_nav_offset_amount : N;
      original_trade_size : N;
      original_sale_condition_modifier : OriginalSaleConditionModifier3.t;
      consolidated_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (original_trade_control_number record) = 10 /\
      (original_proxy_price record < 256 ^ N.of_nat 4)%N /\
      (original_nav_offset_amount record < 256 ^ N.of_nat 4)%N /\
      (original_trade_size record < 256 ^ N.of_nat 4)%N /\
      OriginalSaleConditionModifier3.bounded (original_sale_condition_modifier record) /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (original_trade_control_number record) ++
      encode_uint 4 (original_proxy_price record) ++
      encode_uint 4 (original_nav_offset_amount record) ++
      encode_uint 4 (original_trade_size record) ++
      OriginalSaleConditionModifier3.encode (original_sale_condition_modifier record) ++
      encode_uint 8 (consolidated_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (original_trade_control_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (original_proxy_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (original_nav_offset_amount_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (original_trade_size_value, bytes) =>
                                  match OriginalSaleConditionModifier3.decode bytes with
                                  | None => None
                                  | Some (original_sale_condition_modifier_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (consolidated_volume_value, bytes) =>
                                          Some ({| market_center := market_center_value; issue_symbol := issue_symbol_value; security_class := security_class_value; original_trade_control_number := original_trade_control_number_value; original_proxy_price := original_proxy_price_value; original_nav_offset_amount := original_nav_offset_amount_value; original_trade_size := original_trade_size_value; original_sale_condition_modifier := original_sale_condition_modifier_value; consolidated_volume := consolidated_volume_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !OriginalSaleConditionModifier3.encode_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite OriginalSaleConditionModifier3.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OriginalSaleConditionModifier3.eq_dec]. Defined.

  End NextSharesTradeCancelErrorMessage.

  Module OriginalSaleConditionModifier4.

    (** The sale condition modifier reported on the original trade transaction *)
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

  End OriginalSaleConditionModifier4.

  Module CorrectedSaleConditionModifier.

    (** The sale condition modifier reported on the corrected trade transaction *)
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

    (** Indicates that a previously reported trade transaction has been corrected, carrying both the original and the corrected transaction. *)
    Record t := {
      originating_market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      original_trade_control_number : list byte;
      original_trade_price : N;
      original_trade_size : N;
      original_sale_condition_modifier : OriginalSaleConditionModifier4.t;
      corrected_trade_control_number : list byte;
      corrected_trade_price : N;
      corrected_trade_size : N;
      corrected_sale_condition_modifier : CorrectedSaleConditionModifier.t;
      consolidated_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (original_trade_control_number record) = 10 /\
      (original_trade_price record < 256 ^ N.of_nat 4)%N /\
      (original_trade_size record < 256 ^ N.of_nat 4)%N /\
      OriginalSaleConditionModifier4.bounded (original_sale_condition_modifier record) /\
      Datatypes.length (corrected_trade_control_number record) = 10 /\
      (corrected_trade_price record < 256 ^ N.of_nat 4)%N /\
      (corrected_trade_size record < 256 ^ N.of_nat 4)%N /\
      CorrectedSaleConditionModifier.bounded (corrected_sale_condition_modifier record) /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (original_trade_control_number record) ++
      encode_uint 4 (original_trade_price record) ++
      encode_uint 4 (original_trade_size record) ++
      OriginalSaleConditionModifier4.encode (original_sale_condition_modifier record) ++
      encode_bytes 10 (corrected_trade_control_number record) ++
      encode_uint 4 (corrected_trade_price record) ++
      encode_uint 4 (corrected_trade_size record) ++
      CorrectedSaleConditionModifier.encode (corrected_sale_condition_modifier record) ++
      encode_uint 8 (consolidated_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (originating_market_center_identifier_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (original_trade_control_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (original_trade_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (original_trade_size_value, bytes) =>
                              match OriginalSaleConditionModifier4.decode bytes with
                              | None => None
                              | Some (original_sale_condition_modifier_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (corrected_trade_control_number_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (corrected_trade_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (corrected_trade_size_value, bytes) =>
                                              match CorrectedSaleConditionModifier.decode bytes with
                                              | None => None
                                              | Some (corrected_sale_condition_modifier_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (consolidated_volume_value, bytes) =>
                                                      Some ({| originating_market_center_identifier := originating_market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; original_trade_control_number := original_trade_control_number_value; original_trade_price := original_trade_price_value; original_trade_size := original_trade_size_value; original_sale_condition_modifier := original_sale_condition_modifier_value; corrected_trade_control_number := corrected_trade_control_number_value; corrected_trade_price := corrected_trade_price_value; corrected_trade_size := corrected_trade_size_value; corrected_sale_condition_modifier := corrected_sale_condition_modifier_value; consolidated_volume := consolidated_volume_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !OriginalSaleConditionModifier4.encode_length, !CorrectedSaleConditionModifier.encode_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite OriginalSaleConditionModifier4.decode_encode by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite CorrectedSaleConditionModifier.decode_encode by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OriginalSaleConditionModifier4.eq_dec | apply CorrectedSaleConditionModifier.eq_dec]. Defined.

  End TradeCorrectionMessage.

  Module OriginalSaleConditionModifier5.

    (** The sale condition modifier reported on the original trade transaction *)
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

  End OriginalSaleConditionModifier5.

  Module CorrectedSaleConditionModifier2.

    (** The sale condition modifier reported on the corrected trade transaction *)
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

  End CorrectedSaleConditionModifier2.

  Module LongFormTradeCorrectionMessage.

    (** Trade Correction carrying eight byte original and corrected trade prices. *)
    Record t := {
      originating_market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      original_trade_control_number : list byte;
      original_trade_price_long : N;
      original_trade_size : N;
      original_sale_condition_modifier : OriginalSaleConditionModifier5.t;
      corrected_trade_control_number : list byte;
      corrected_trade_price_long : N;
      corrected_trade_size : N;
      corrected_sale_condition_modifier : CorrectedSaleConditionModifier2.t;
      consolidated_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (original_trade_control_number record) = 10 /\
      (original_trade_price_long record < 256 ^ N.of_nat 8)%N /\
      (original_trade_size record < 256 ^ N.of_nat 4)%N /\
      OriginalSaleConditionModifier5.bounded (original_sale_condition_modifier record) /\
      Datatypes.length (corrected_trade_control_number record) = 10 /\
      (corrected_trade_price_long record < 256 ^ N.of_nat 8)%N /\
      (corrected_trade_size record < 256 ^ N.of_nat 4)%N /\
      CorrectedSaleConditionModifier2.bounded (corrected_sale_condition_modifier record) /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (original_trade_control_number record) ++
      encode_uint 8 (original_trade_price_long record) ++
      encode_uint 4 (original_trade_size record) ++
      OriginalSaleConditionModifier5.encode (original_sale_condition_modifier record) ++
      encode_bytes 10 (corrected_trade_control_number record) ++
      encode_uint 8 (corrected_trade_price_long record) ++
      encode_uint 4 (corrected_trade_size record) ++
      CorrectedSaleConditionModifier2.encode (corrected_sale_condition_modifier record) ++
      encode_uint 8 (consolidated_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (originating_market_center_identifier_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (original_trade_control_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_trade_price_long_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (original_trade_size_value, bytes) =>
                              match OriginalSaleConditionModifier5.decode bytes with
                              | None => None
                              | Some (original_sale_condition_modifier_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (corrected_trade_control_number_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (corrected_trade_price_long_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (corrected_trade_size_value, bytes) =>
                                              match CorrectedSaleConditionModifier2.decode bytes with
                                              | None => None
                                              | Some (corrected_sale_condition_modifier_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (consolidated_volume_value, bytes) =>
                                                      Some ({| originating_market_center_identifier := originating_market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; original_trade_control_number := original_trade_control_number_value; original_trade_price_long := original_trade_price_long_value; original_trade_size := original_trade_size_value; original_sale_condition_modifier := original_sale_condition_modifier_value; corrected_trade_control_number := corrected_trade_control_number_value; corrected_trade_price_long := corrected_trade_price_long_value; corrected_trade_size := corrected_trade_size_value; corrected_sale_condition_modifier := corrected_sale_condition_modifier_value; consolidated_volume := consolidated_volume_value |}, bytes)
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !OriginalSaleConditionModifier5.encode_length, !CorrectedSaleConditionModifier2.encode_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite OriginalSaleConditionModifier5.decode_encode by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite CorrectedSaleConditionModifier2.decode_encode by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OriginalSaleConditionModifier5.eq_dec | apply CorrectedSaleConditionModifier2.eq_dec]. Defined.

  End LongFormTradeCorrectionMessage.

  Module OriginalSaleConditionModifier6.

    (** The sale condition modifier reported on the original trade transaction *)
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

  End OriginalSaleConditionModifier6.

  Module CorrectedSaleConditionModifier3.

    (** The sale condition modifier reported on the corrected trade transaction *)
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

  End CorrectedSaleConditionModifier3.

  Module NextSharesTradeCorrectionMessage.

    (** Indicates that a previously reported NextShares trade transaction has been corrected. *)
    Record t := {
      market_center : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      original_trade_control_number : list byte;
      original_proxy_price : N;
      original_nav_offset_amount : N;
      original_trade_size : N;
      original_sale_condition_modifier : OriginalSaleConditionModifier6.t;
      corrected_trade_control_number : list byte;
      corrected_proxy_price : N;
      corrected_nav_offset_amount : N;
      corrected_trade_size : N;
      corrected_sale_condition_modifier : CorrectedSaleConditionModifier3.t;
      consolidated_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (original_trade_control_number record) = 10 /\
      (original_proxy_price record < 256 ^ N.of_nat 4)%N /\
      (original_nav_offset_amount record < 256 ^ N.of_nat 4)%N /\
      (original_trade_size record < 256 ^ N.of_nat 4)%N /\
      OriginalSaleConditionModifier6.bounded (original_sale_condition_modifier record) /\
      Datatypes.length (corrected_trade_control_number record) = 10 /\
      (corrected_proxy_price record < 256 ^ N.of_nat 4)%N /\
      (corrected_nav_offset_amount record < 256 ^ N.of_nat 4)%N /\
      (corrected_trade_size record < 256 ^ N.of_nat 4)%N /\
      CorrectedSaleConditionModifier3.bounded (corrected_sale_condition_modifier record) /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (original_trade_control_number record) ++
      encode_uint 4 (original_proxy_price record) ++
      encode_uint 4 (original_nav_offset_amount record) ++
      encode_uint 4 (original_trade_size record) ++
      OriginalSaleConditionModifier6.encode (original_sale_condition_modifier record) ++
      encode_bytes 10 (corrected_trade_control_number record) ++
      encode_uint 4 (corrected_proxy_price record) ++
      encode_uint 4 (corrected_nav_offset_amount record) ++
      encode_uint 4 (corrected_trade_size record) ++
      CorrectedSaleConditionModifier3.encode (corrected_sale_condition_modifier record) ++
      encode_uint 8 (consolidated_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (original_trade_control_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (original_proxy_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (original_nav_offset_amount_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (original_trade_size_value, bytes) =>
                                  match OriginalSaleConditionModifier6.decode bytes with
                                  | None => None
                                  | Some (original_sale_condition_modifier_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (corrected_trade_control_number_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (corrected_proxy_price_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (corrected_nav_offset_amount_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (corrected_trade_size_value, bytes) =>
                                                      match CorrectedSaleConditionModifier3.decode bytes with
                                                      | None => None
                                                      | Some (corrected_sale_condition_modifier_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (consolidated_volume_value, bytes) =>
                                                              Some ({| market_center := market_center_value; issue_symbol := issue_symbol_value; security_class := security_class_value; original_trade_control_number := original_trade_control_number_value; original_proxy_price := original_proxy_price_value; original_nav_offset_amount := original_nav_offset_amount_value; original_trade_size := original_trade_size_value; original_sale_condition_modifier := original_sale_condition_modifier_value; corrected_trade_control_number := corrected_trade_control_number_value; corrected_proxy_price := corrected_proxy_price_value; corrected_nav_offset_amount := corrected_nav_offset_amount_value; corrected_trade_size := corrected_trade_size_value; corrected_sale_condition_modifier := corrected_sale_condition_modifier_value; consolidated_volume := consolidated_volume_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !OriginalSaleConditionModifier6.encode_length, !CorrectedSaleConditionModifier3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite OriginalSaleConditionModifier6.decode_encode by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite CorrectedSaleConditionModifier3.decode_encode by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OriginalSaleConditionModifier6.eq_dec | apply CorrectedSaleConditionModifier3.eq_dec]. Defined.

  End NextSharesTradeCorrectionMessage.

  Module StockTradingActionMessage.

    (** Indicates the current trading status of a security to the trading community. Clients should initialize all securities as halted at the start of the session. *)
    Record t := {
      reserved : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      current_trading_state : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (current_trading_state record) = 1 /\
      Datatypes.length (reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reserved record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 1 (current_trading_state record) ++
      encode_bytes 4 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reserved_value, bytes) =>
          match decode_bytes 8 bytes with
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
                          Some ({| reserved := reserved_value; issue_symbol := issue_symbol_value; security_class := security_class_value; current_trading_state := current_trading_state_value; reason := reason_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockTradingActionMessage.

  Module StockDirectoryMessage.

    (** Identifies the securities eligible for the trading session, disseminated at the start of each day. *)
    Record t := {
      stock : list byte;
      market_category : list byte;
      financial_status_indicator : list byte;
      round_lot_size : N;
      round_lots_only : list byte;
      issue_classification : list byte;
      issue_sub_type : list byte;
      authenticity : list byte;
      short_sale_threshold_indicator : list byte;
      ipo_flag : list byte;
      luld_reference_price_tier : list byte;
      etp_flag : list byte;
      etp_leverage_factor : N;
      inverse_indicator : list byte;
      bloomberg_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (market_category record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      (round_lot_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (round_lots_only record) = 1 /\
      Datatypes.length (issue_classification record) = 1 /\
      Datatypes.length (issue_sub_type record) = 2 /\
      Datatypes.length (authenticity record) = 1 /\
      Datatypes.length (short_sale_threshold_indicator record) = 1 /\
      Datatypes.length (ipo_flag record) = 1 /\
      Datatypes.length (luld_reference_price_tier record) = 1 /\
      Datatypes.length (etp_flag record) = 1 /\
      (etp_leverage_factor record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (inverse_indicator record) = 1 /\
      Datatypes.length (bloomberg_id record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (market_category record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_uint 4 (round_lot_size record) ++
      encode_bytes 1 (round_lots_only record) ++
      encode_bytes 1 (issue_classification record) ++
      encode_bytes 2 (issue_sub_type record) ++
      encode_bytes 1 (authenticity record) ++
      encode_bytes 1 (short_sale_threshold_indicator record) ++
      encode_bytes 1 (ipo_flag record) ++
      encode_bytes 1 (luld_reference_price_tier record) ++
      encode_bytes 1 (etp_flag record) ++
      encode_uint 4 (etp_leverage_factor record) ++
      encode_bytes 1 (inverse_indicator record) ++
      encode_bytes 12 (bloomberg_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_category_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (financial_status_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (round_lot_size_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (round_lots_only_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (issue_classification_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (issue_sub_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (authenticity_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (short_sale_threshold_indicator_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (ipo_flag_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (luld_reference_price_tier_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (etp_flag_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (etp_leverage_factor_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (inverse_indicator_value, bytes) =>
                                                              match decode_bytes 12 bytes with
                                                              | None => None
                                                              | Some (bloomberg_id_value, bytes) =>
                                                                  Some ({| stock := stock_value; market_category := market_category_value; financial_status_indicator := financial_status_indicator_value; round_lot_size := round_lot_size_value; round_lots_only := round_lots_only_value; issue_classification := issue_classification_value; issue_sub_type := issue_sub_type_value; authenticity := authenticity_value; short_sale_threshold_indicator := short_sale_threshold_indicator_value; ipo_flag := ipo_flag_value; luld_reference_price_tier := luld_reference_price_tier_value; etp_flag := etp_flag_value; etp_leverage_factor := etp_leverage_factor_value; inverse_indicator := inverse_indicator_value; bloomberg_id := bloomberg_id_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockDirectoryMessage.

  Module RegShoShortSalePriceTestRestrictedIndicatorMessage.

    (** Indicates the Reg Sho short sale price test restriction status for an issue, under Rule 201 of Regulation Sho. *)
    Record t := {
      issue_symbol : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (issue_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reg_sho_action_value, bytes) =>
              Some ({| issue_symbol := issue_symbol_value; reg_sho_action := reg_sho_action_value |}, bytes)
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

  End RegShoShortSalePriceTestRestrictedIndicatorMessage.

  Module AdjustedClosingPriceMessage.

    (** Denotes the adjusted previous close price to be used for intraday net change calculations. *)
    Record t := {
      issue_symbol : list byte;
      security_class : list byte;
      adjusted_closing_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      (adjusted_closing_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_uint 4 (adjusted_closing_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (issue_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (security_class_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (adjusted_closing_price_value, bytes) =>
                  Some ({| issue_symbol := issue_symbol_value; security_class := security_class_value; adjusted_closing_price := adjusted_closing_price_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AdjustedClosingPriceMessage.

  Module LongFormAdjustedClosingPriceMessage.

    (** Adjusted Closing Price carrying an eight byte price. *)
    Record t := {
      issue_symbol : list byte;
      security_class : list byte;
      adjusted_closing_price_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      (adjusted_closing_price_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_uint 8 (adjusted_closing_price_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (issue_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (security_class_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (adjusted_closing_price_long_value, bytes) =>
                  Some ({| issue_symbol := issue_symbol_value; security_class := security_class_value; adjusted_closing_price_long := adjusted_closing_price_long_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongFormAdjustedClosingPriceMessage.

  Module EndOfDayTradeSummaryMessage.

    (** Summarises the consolidated trading activity for an issue at the end of the trading day. *)
    Record t := {
      issue_symbol : list byte;
      market_category : list byte;
      consolidated_high_price : N;
      consolidated_low_price : N;
      consolidated_closing_price : N;
      consolidated_volume : N;
      consolidated_open_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (market_category record) = 1 /\
      (consolidated_high_price record < 256 ^ N.of_nat 4)%N /\
      (consolidated_low_price record < 256 ^ N.of_nat 4)%N /\
      (consolidated_closing_price record < 256 ^ N.of_nat 4)%N /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N /\
      (consolidated_open_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (market_category record) ++
      encode_uint 4 (consolidated_high_price record) ++
      encode_uint 4 (consolidated_low_price record) ++
      encode_uint 4 (consolidated_closing_price record) ++
      encode_uint 8 (consolidated_volume record) ++
      encode_uint 4 (consolidated_open_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (issue_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_category_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (consolidated_high_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (consolidated_low_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (consolidated_closing_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (consolidated_volume_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (consolidated_open_price_value, bytes) =>
                                  Some ({| issue_symbol := issue_symbol_value; market_category := market_category_value; consolidated_high_price := consolidated_high_price_value; consolidated_low_price := consolidated_low_price_value; consolidated_closing_price := consolidated_closing_price_value; consolidated_volume := consolidated_volume_value; consolidated_open_price := consolidated_open_price_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfDayTradeSummaryMessage.

  Module LongFormEndOfDayTradeSummaryMessage.

    (** End of Day Trade Summary carrying eight byte prices. *)
    Record t := {
      issue_symbol : list byte;
      market_category : list byte;
      consolidated_high_price_long : N;
      consolidated_low_price_long : N;
      consolidated_closing_price_long : N;
      consolidated_volume : N;
      consolidated_open_price_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (market_category record) = 1 /\
      (consolidated_high_price_long record < 256 ^ N.of_nat 8)%N /\
      (consolidated_low_price_long record < 256 ^ N.of_nat 8)%N /\
      (consolidated_closing_price_long record < 256 ^ N.of_nat 8)%N /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N /\
      (consolidated_open_price_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (market_category record) ++
      encode_uint 8 (consolidated_high_price_long record) ++
      encode_uint 8 (consolidated_low_price_long record) ++
      encode_uint 8 (consolidated_closing_price_long record) ++
      encode_uint 8 (consolidated_volume record) ++
      encode_uint 8 (consolidated_open_price_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (issue_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_category_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (consolidated_high_price_long_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (consolidated_low_price_long_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (consolidated_closing_price_long_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (consolidated_volume_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (consolidated_open_price_long_value, bytes) =>
                                  Some ({| issue_symbol := issue_symbol_value; market_category := market_category_value; consolidated_high_price_long := consolidated_high_price_long_value; consolidated_low_price_long := consolidated_low_price_long_value; consolidated_closing_price_long := consolidated_closing_price_long_value; consolidated_volume := consolidated_volume_value; consolidated_open_price_long := consolidated_open_price_long_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongFormEndOfDayTradeSummaryMessage.

  Module NextSharesEndOfDayTradeSummaryMessage.

    (** Summarises the consolidated trading activity for a NextShares issue, each price paired with the Nav offset to apply to it. *)
    Record t := {
      issue_symbol : list byte;
      market_category : list byte;
      consolidated_high_price : N;
      nav_offset_amount_high : N;
      consolidated_low_price : N;
      nav_offset_amount_low : N;
      consolidated_closing_price : N;
      nav_offset_amount_closing : N;
      consolidated_volume : N;
      consolidated_open_price : N;
      nav_offset_amount_open : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (market_category record) = 1 /\
      (consolidated_high_price record < 256 ^ N.of_nat 4)%N /\
      (nav_offset_amount_high record < 256 ^ N.of_nat 4)%N /\
      (consolidated_low_price record < 256 ^ N.of_nat 4)%N /\
      (nav_offset_amount_low record < 256 ^ N.of_nat 4)%N /\
      (consolidated_closing_price record < 256 ^ N.of_nat 4)%N /\
      (nav_offset_amount_closing record < 256 ^ N.of_nat 4)%N /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N /\
      (consolidated_open_price record < 256 ^ N.of_nat 4)%N /\
      (nav_offset_amount_open record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (market_category record) ++
      encode_uint 4 (consolidated_high_price record) ++
      encode_uint 4 (nav_offset_amount_high record) ++
      encode_uint 4 (consolidated_low_price record) ++
      encode_uint 4 (nav_offset_amount_low record) ++
      encode_uint 4 (consolidated_closing_price record) ++
      encode_uint 4 (nav_offset_amount_closing record) ++
      encode_uint 8 (consolidated_volume record) ++
      encode_uint 4 (consolidated_open_price record) ++
      encode_uint 4 (nav_offset_amount_open record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (issue_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_category_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (consolidated_high_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (nav_offset_amount_high_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (consolidated_low_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (nav_offset_amount_low_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (consolidated_closing_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (nav_offset_amount_closing_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (consolidated_volume_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (consolidated_open_price_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (nav_offset_amount_open_value, bytes) =>
                                                  Some ({| issue_symbol := issue_symbol_value; market_category := market_category_value; consolidated_high_price := consolidated_high_price_value; nav_offset_amount_high := nav_offset_amount_high_value; consolidated_low_price := consolidated_low_price_value; nav_offset_amount_low := nav_offset_amount_low_value; consolidated_closing_price := consolidated_closing_price_value; nav_offset_amount_closing := nav_offset_amount_closing_value; consolidated_volume := consolidated_volume_value; consolidated_open_price := consolidated_open_price_value; nav_offset_amount_open := nav_offset_amount_open_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NextSharesEndOfDayTradeSummaryMessage.

  Module IpoInformationMessage.

    (** Denotes the reference price to be used for intraday net change calculations for an issue. *)
    Record t := {
      issue_symbol : list byte;
      security_class : list byte;
      reference_for_net_change : list byte;
      reference_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (reference_for_net_change record) = 1 /\
      (reference_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 1 (reference_for_net_change record) ++
      encode_uint 4 (reference_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (issue_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (security_class_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reference_for_net_change_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (reference_price_value, bytes) =>
                      Some ({| issue_symbol := issue_symbol_value; security_class := security_class_value; reference_for_net_change := reference_for_net_change_value; reference_price := reference_price_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IpoInformationMessage.

  Module MwcbDeclineLevelMessage.

    (** Informs the market of the daily market wide circuit breaker decline levels, disseminated at the start of the trading day. *)
    Record t := {
      level_1 : N;
      level_2 : N;
      level_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (level_1 record < 256 ^ N.of_nat 8)%N /\
      (level_2 record < 256 ^ N.of_nat 8)%N /\
      (level_3 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (level_1 record) ++
      encode_uint 8 (level_2 record) ++
      encode_uint 8 (level_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (level_1_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (level_2_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (level_3_value, bytes) =>
                  Some ({| level_1 := level_1_value; level_2 := level_2_value; level_3 := level_3_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MwcbDeclineLevelMessage.

  Module MwcbStatusMessage.

    (** Informs the market that a market wide circuit breaker decline level has been breached. *)
    Record t := {
      breached_level : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (breached_level record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (breached_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (breached_level_value, bytes) =>
          Some ({| breached_level := breached_level_value |}, bytes)
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

  End MwcbStatusMessage.

  Module IpoQuotingPeriodUpdateMessage.

    (** Indicates the anticipated Ipo quotation release time of a security. *)
    Record t := {
      stock : list byte;
      ipo_quotation_release_time : N;
      ipo_quotation_release_qualifier : list byte;
      ipo_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 8 /\
      (ipo_quotation_release_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ipo_quotation_release_qualifier record) = 1 /\
      (ipo_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock record) ++
      encode_uint 4 (ipo_quotation_release_time record) ++
      encode_bytes 1 (ipo_quotation_release_qualifier record) ++
      encode_uint 4 (ipo_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (ipo_quotation_release_time_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (ipo_quotation_release_qualifier_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ipo_price_value, bytes) =>
                      Some ({| stock := stock_value; ipo_quotation_release_time := ipo_quotation_release_time_value; ipo_quotation_release_qualifier := ipo_quotation_release_qualifier_value; ipo_price := ipo_price_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IpoQuotingPeriodUpdateMessage.

  Module OperationalHaltMessage.

    (** Indicates the current operational status of a security to the trading community. An operational halt is specific to the market centre for which it is declared and does not interrupt trading of the instrument on any other market place. *)
    Record t := {
      stock : list byte;
      market_code : list byte;
      operational_halt_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (market_code record) = 1 /\
      Datatypes.length (operational_halt_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (market_code record) ++
      encode_bytes 1 (operational_halt_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_code_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (operational_halt_action_value, bytes) =>
                  Some ({| stock := stock_value; market_code := market_code_value; operational_halt_action := operational_halt_action_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End OperationalHaltMessage.

End NsmEquitiesNlsPlusV30.
