From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The Securities Industry Automation Corporation Output

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
      - a Composite rule
      - a run counted by a field
      - the dispatch that chooses a message by its type
  *)

Module SiacCtsOutputV210.

  Module SaleConditions.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions.

  Module SaleConditions2.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions2.

  Module SaleConditions3.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions3.

  Module SaleConditions4.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions4.

  Module SaleConditions5.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions5.

  Module SaleConditions6.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions6.

  Module SaleConditions7.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions7.

  Module SaleConditions8.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions8.

  Module SaleConditions9.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions9.

  Module CorrectedTrade.

    (** Corrected Trade *)
    Record t := {
      sale_conditions : SaleConditions9.t;
      trade_price : N;
      trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SaleConditions9.bounded (sale_conditions record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      SaleConditions9.encode (sale_conditions record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SaleConditions9.decode bytes with
      | None => None
      | Some (sale_conditions_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_volume_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (sellers_sale_days_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (stop_stock_indicator_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (trade_through_exempt_indicator_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (short_sale_restriction_indicator_value, bytes) =>
                                  Some ({| sale_conditions := sale_conditions_value; trade_price := trade_price_value; trade_volume := trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SaleConditions9.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SaleConditions9.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditions9.eq_dec]. Defined.

  End CorrectedTrade.

  Module SaleConditions10.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions10.

  Module OriginalTrade.

    (** Original Trade *)
    Record t := {
      sale_conditions : SaleConditions10.t;
      trade_price : N;
      trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SaleConditions10.bounded (sale_conditions record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      SaleConditions10.encode (sale_conditions record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SaleConditions10.decode bytes with
      | None => None
      | Some (sale_conditions_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_volume_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (sellers_sale_days_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (stop_stock_indicator_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (trade_through_exempt_indicator_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (short_sale_restriction_indicator_value, bytes) =>
                                  Some ({| sale_conditions := sale_conditions_value; trade_price := trade_price_value; trade_volume := trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SaleConditions10.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SaleConditions10.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditions10.eq_dec]. Defined.

  End OriginalTrade.

  Module ConsolidatedData.

    (** Consolidated Data *)
    Record t := {
      previous_close_price_date : N;
      last_participant_id : list byte;
      last_price : N;
      high_price : N;
      low_price : N;
      total_volume_short : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (last_participant_id record) = 1 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (total_volume_short record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_bytes 1 (last_participant_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 4 (total_volume_short record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_participant_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (high_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (low_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (total_volume_short_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_participant_id := last_participant_id_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; total_volume_short := total_volume_short_value; tick := tick_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConsolidatedData.

  Module ParticipantData.

    (** Participant Data *)
    Record t := {
      previous_close_price_date : N;
      last_price : N;
      high_price : N;
      low_price : N;
      open_price : N;
      total_volume_short : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (total_volume_short record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (open_price record) ++
      encode_uint 4 (total_volume_short record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (last_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (high_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (low_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (open_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (total_volume_short_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; open_price := open_price_value; total_volume_short := total_volume_short_value; tick := tick_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ParticipantData.

  Module SaleConditions11.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions11.

  Module FractionalCorrectedTrade.

    (** Fractional Corrected Trade *)
    Record t := {
      sale_conditions : SaleConditions11.t;
      trade_price : N;
      fractional_trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SaleConditions11.bounded (sale_conditions record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      SaleConditions11.encode (sale_conditions record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SaleConditions11.decode bytes with
      | None => None
      | Some (sale_conditions_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (fractional_trade_volume_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (sellers_sale_days_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (stop_stock_indicator_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (trade_through_exempt_indicator_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (short_sale_restriction_indicator_value, bytes) =>
                                  Some ({| sale_conditions := sale_conditions_value; trade_price := trade_price_value; fractional_trade_volume := fractional_trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SaleConditions11.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SaleConditions11.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditions11.eq_dec]. Defined.

  End FractionalCorrectedTrade.

  Module SaleConditions12.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions12.

  Module FractionalOriginalTrade.

    (** Fractional Original Trade *)
    Record t := {
      sale_conditions : SaleConditions12.t;
      trade_price : N;
      fractional_trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SaleConditions12.bounded (sale_conditions record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      SaleConditions12.encode (sale_conditions record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SaleConditions12.decode bytes with
      | None => None
      | Some (sale_conditions_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (fractional_trade_volume_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (sellers_sale_days_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (stop_stock_indicator_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (trade_through_exempt_indicator_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (short_sale_restriction_indicator_value, bytes) =>
                                  Some ({| sale_conditions := sale_conditions_value; trade_price := trade_price_value; fractional_trade_volume := fractional_trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SaleConditions12.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SaleConditions12.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditions12.eq_dec]. Defined.

  End FractionalOriginalTrade.

  Module FractionalConsolidatedData.

    (** Fractional Consolidated Data *)
    Record t := {
      previous_close_price_date : N;
      last_participant_id : list byte;
      last_price : N;
      high_price : N;
      low_price : N;
      fractional_total_volume : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (last_participant_id record) = 1 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_bytes 1 (last_participant_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (fractional_total_volume record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_participant_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (high_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (low_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (fractional_total_volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_participant_id := last_participant_id_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; fractional_total_volume := fractional_total_volume_value; tick := tick_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FractionalConsolidatedData.

  Module FractionalParticipantData.

    (** Fractional Participant Data *)
    Record t := {
      previous_close_price_date : N;
      last_price : N;
      high_price : N;
      low_price : N;
      open_price : N;
      fractional_total_volume : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (open_price record) ++
      encode_uint 8 (fractional_total_volume record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (last_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (high_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (low_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (open_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (fractional_total_volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; open_price := open_price_value; fractional_total_volume := fractional_total_volume_value; tick := tick_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FractionalParticipantData.

  Module SaleConditions13.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions13.

  Module SaleConditions14.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions14.

  Module SaleConditions15.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions15.

  Module ConsolidatedData2.

    (** Consolidated Data *)
    Record t := {
      previous_close_price_date : N;
      last_participant_id : list byte;
      last_price : N;
      high_price : N;
      low_price : N;
      total_volume_short : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (last_participant_id record) = 1 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (total_volume_short record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_bytes 1 (last_participant_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 4 (total_volume_short record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_participant_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (high_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (low_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (total_volume_short_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_participant_id := last_participant_id_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; total_volume_short := total_volume_short_value; tick := tick_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConsolidatedData2.

  Module ParticipantData2.

    (** Participant Data *)
    Record t := {
      previous_close_price_date : N;
      last_price : N;
      high_price : N;
      low_price : N;
      open_price : N;
      total_volume_short : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (total_volume_short record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (open_price record) ++
      encode_uint 4 (total_volume_short record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (last_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (high_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (low_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (open_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (total_volume_short_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; open_price := open_price_value; total_volume_short := total_volume_short_value; tick := tick_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ParticipantData2.

  Module SaleConditions16.

    (** Sale Conditions *)
    Record t := {
      settlement_type : list byte;
      trade_through_exempt_reason : list byte;
      extended_hours_or_sequence_type : list byte;
      sro_trade_detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (trade_through_exempt_reason record) = 1 /\
      Datatypes.length (extended_hours_or_sequence_type record) = 1 /\
      Datatypes.length (sro_trade_detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (trade_through_exempt_reason record) ++
      encode_bytes 1 (extended_hours_or_sequence_type record) ++
      encode_bytes 1 (sro_trade_detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (settlement_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_through_exempt_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (extended_hours_or_sequence_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sro_trade_detail_value, bytes) =>
                      Some ({| settlement_type := settlement_type_value; trade_through_exempt_reason := trade_through_exempt_reason_value; extended_hours_or_sequence_type := extended_hours_or_sequence_type_value; sro_trade_detail := sro_trade_detail_value |}, bytes)
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

  End SaleConditions16.

  Module FractionalConsolidatedData2.

    (** Fractional Consolidated Data *)
    Record t := {
      previous_close_price_date : N;
      last_participant_id : list byte;
      last_price : N;
      high_price : N;
      low_price : N;
      fractional_total_volume : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (last_participant_id record) = 1 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_bytes 1 (last_participant_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (fractional_total_volume record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_participant_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (high_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (low_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (fractional_total_volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_participant_id := last_participant_id_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; fractional_total_volume := fractional_total_volume_value; tick := tick_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FractionalConsolidatedData2.

  Module FractionalParticipantData2.

    (** Fractional Participant Data *)
    Record t := {
      previous_close_price_date : N;
      last_price : N;
      high_price : N;
      low_price : N;
      open_price : N;
      fractional_total_volume : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (open_price record) ++
      encode_uint 8 (fractional_total_volume record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (last_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (high_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (low_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (open_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (fractional_total_volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; open_price := open_price_value; fractional_total_volume := fractional_total_volume_value; tick := tick_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FractionalParticipantData2.

End SiacCtsOutputV210.
