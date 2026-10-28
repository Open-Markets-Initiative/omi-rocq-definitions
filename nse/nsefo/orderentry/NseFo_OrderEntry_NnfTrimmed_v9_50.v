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

Module NseFoOrderEntryV950.

  Module ContractDescTr.

    (** CONTRACT_DESC_TR *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDescTr.

  Module ContractDescTr2.

    (** CONTRACT_DESC_TR *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDescTr2.

  Module ContractDescTr3.

    (** CONTRACT_DESC_TR *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDescTr3.

  Module ContractDescTr4.

    (** CONTRACT_DESC_TR *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDescTr4.

  Module QuickAcknowledgementMessage.

    (** Immediate acknowledgement that an order related request reached the exchange *)
    Record t := {
      trader_id : N;
      time_stamp : N;
      reference : N;
      error_code : N;
      message_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      (time_stamp record < 256 ^ N.of_nat 8)%N /\
      (reference record < 256 ^ N.of_nat 4)%N /\
      (error_code record < 256 ^ N.of_nat 2)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (trader_id record) ++
      encode_uint 8 (time_stamp record) ++
      encode_uint 4 (reference record) ++
      encode_uint 2 (error_code record) ++
      encode_uint 2 (message_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (trader_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (time_stamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (reference_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (error_code_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (message_length_value, bytes) =>
                          Some ({| trader_id := trader_id_value; time_stamp := time_stamp_value; reference := reference_value; error_code := error_code_value; message_length := message_length_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End QuickAcknowledgementMessage.

End NseFoOrderEntryV950.
