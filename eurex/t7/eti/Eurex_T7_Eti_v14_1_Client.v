From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Eurex Exchange Enhanced Trading Interface

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
      - a run counted by a field
  *)

Module EurexT7EtiV141Client.

  Module MessageHeader.

    (** Eurex T7 Eti message header *)
    Record t := {
      body_len : N;
      template_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (body_len record < 256 ^ N.of_nat 4)%N /\
      (template_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (body_len record) ++
      encode_uint 2 (template_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (body_len_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              Some ({| body_len := body_len_value; template_id := template_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MessageHeader.

  Module RequestHeaderComp.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp.

  Module RequestHeaderComp2.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp2.

  Module RequestHeaderComp3.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp3.

  Module RequestHeaderComp4.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp4.

  Module RequestHeaderComp5.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp5.

  Module RequestHeaderComp6.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp6.

  Module RequestHeaderComp7.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp7.

  Module RequestHeaderComp8.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp8.

  Module OldBasketDataGrpComp.

    Record t := {
      basket_trd_match_id : N;
      basket_exec_id : N;
      trade_report_id : list byte;
      maturity_month_year : N;
      basket_trade_report_type : N;
      basket_trade_report_text : list byte;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (basket_trd_match_id record < 256 ^ N.of_nat 8)%N /\
      (basket_exec_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_report_id record) = 20 /\
      (maturity_month_year record < 256 ^ N.of_nat 4)%N /\
      (basket_trade_report_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (basket_trade_report_text record) = 20 /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (basket_trd_match_id record) ++
      encode_uint 4 (basket_exec_id record) ++
      encode_bytes 20 (trade_report_id record) ++
      encode_uint 4 (maturity_month_year record) ++
      encode_uint 1 (basket_trade_report_type record) ++
      encode_bytes 20 (basket_trade_report_text record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (basket_trd_match_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (basket_exec_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (trade_report_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (maturity_month_year_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (basket_trade_report_type_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (basket_trade_report_text_value, bytes) =>
                              match decode_uint 7 bytes with
                              | None => None
                              | Some (pad7_value, bytes) =>
                                  Some ({| basket_trd_match_id := basket_trd_match_id_value; basket_exec_id := basket_exec_id_value; trade_report_id := trade_report_id_value; maturity_month_year := maturity_month_year_value; basket_trade_report_type := basket_trade_report_type_value; basket_trade_report_text := basket_trade_report_text_value; pad7 := pad7_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OldBasketDataGrpComp.

  Module NewBasketDataGrpComp.

    Record t := {
      trade_report_id : list byte;
      maturity_month_year : N;
      basket_trade_report_type : N;
      basket_trade_report_text : list byte;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_report_id record) = 20 /\
      (maturity_month_year record < 256 ^ N.of_nat 4)%N /\
      (basket_trade_report_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (basket_trade_report_text record) = 20 /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (trade_report_id record) ++
      encode_uint 4 (maturity_month_year record) ++
      encode_uint 1 (basket_trade_report_type record) ++
      encode_bytes 20 (basket_trade_report_text record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (trade_report_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (maturity_month_year_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (basket_trade_report_type_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (basket_trade_report_text_value, bytes) =>
                      match decode_uint 3 bytes with
                      | None => None
                      | Some (pad3_value, bytes) =>
                          Some ({| trade_report_id := trade_report_id_value; maturity_month_year := maturity_month_year_value; basket_trade_report_type := basket_trade_report_type_value; basket_trade_report_text := basket_trade_report_text_value; pad3 := pad3_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewBasketDataGrpComp.

  Module RequestHeaderComp9.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp9.

  Module RequestHeaderComp10.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp10.

  Module RequestHeaderComp11.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp11.

  Module RequestHeaderComp12.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp12.

  Module RequestHeaderComp13.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp13.

  Module RequestHeaderComp14.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp14.

  Module RequestHeaderComp15.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp15.

  Module RequestHeaderComp16.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp16.

  Module RequestHeaderComp17.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp17.

  Module RequestHeaderComp18.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp18.

  Module RequestHeaderComp19.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp19.

  Module RequestHeaderComp20.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp20.

  Module RequestHeaderComp21.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp21.

  Module RequestHeaderComp22.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp22.

  Module RequestHeaderComp23.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp23.

  Module RequestHeaderComp24.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp24.

  Module RequestHeaderComp25.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp25.

  Module RequestHeaderComp26.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp26.

  Module RequestHeaderComp27.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp27.

  Module RequestHeaderComp28.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp28.

  Module RequestHeaderComp29.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp29.

  Module RequestHeaderComp30.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp30.

  Module RequestHeaderComp31.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp31.

  Module RequestHeaderComp32.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp32.

  Module RequestHeaderComp33.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp33.

  Module RequestHeaderComp34.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp34.

  Module RequestHeaderComp35.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp35.

  Module RequestHeaderComp36.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp36.

  Module RequestHeaderComp37.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp37.

  Module RequestHeaderComp38.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp38.

  Module RequestHeaderComp39.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp39.

  Module RequestHeaderComp40.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp40.

  Module RequestHeaderComp41.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp41.

  Module RequestHeaderComp42.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp42.

  Module RequestHeaderComp43.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp43.

  Module RequestHeaderComp44.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp44.

  Module RequestHeaderComp45.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp45.

  Module RequestHeaderComp46.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp46.

  Module RequestHeaderComp47.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp47.

  Module RequestHeaderComp48.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp48.

  Module RequestHeaderComp49.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp49.

  Module RequestHeaderComp50.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp50.

  Module RequestHeaderComp51.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp51.

  Module RequestHeaderComp52.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp52.

  Module RequestHeaderComp53.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp53.

  Module RequestHeaderComp54.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp54.

  Module RequestHeaderComp55.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp55.

  Module RequestHeaderComp56.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp56.

  Module RequestHeaderComp57.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp57.

  Module RequestHeaderComp58.

    Record t := {
      msg_seq_num : N;
      sender_sub_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sender_sub_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sender_sub_id_value, bytes) =>
              Some ({| msg_seq_num := msg_seq_num_value; sender_sub_id := sender_sub_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestHeaderComp58.

End EurexT7EtiV141Client.
