From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Stock Exchange of India Ltd Order Entry

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
      - a field read in bits
      - a Composite rule
  *)

Module NseCmOrderEntryV66.

  Module SecInfo.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecInfo.

  Module SecInfo2.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecInfo2.

  Module SecInfo3.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecInfo3.

  Module SecInfo4.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecInfo4.

  Module QuickAcknowledgementMessage.

    (** Immediate acknowledgement of a trimmed order entry, modification or cancellation request, answered on the separate port of the gateway router server *)
    Record t := {
      transaction_code : N;
      trader_id : N;
      timestamp : N;
      reference : N;
      error_code : N;
      message_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_code record < 256 ^ N.of_nat 2)%N /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (reference record < 256 ^ N.of_nat 4)%N /\
      (error_code record < 256 ^ N.of_nat 2)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (transaction_code record) ++
      encode_uint 4 (trader_id record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (reference record) ++
      encode_uint 2 (error_code record) ++
      encode_uint 2 (message_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (transaction_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (reference_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (error_code_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (message_length_value, bytes) =>
                              Some ({| transaction_code := transaction_code_value; trader_id := trader_id_value; timestamp := timestamp_value; reference := reference_value; error_code := error_code_value; message_length := message_length_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End QuickAcknowledgementMessage.

End NseCmOrderEntryV66.
