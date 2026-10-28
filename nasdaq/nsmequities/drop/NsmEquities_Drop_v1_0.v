From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Drop

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
  *)

Module NsmEquitiesDropV10.

  Module MessageHeader.

    (** Time Stamp and Type opening every Drop message line *)
    Record t := {
      time_stamp : list byte;
      comma : list byte;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (time_stamp record) = 9 /\
      Datatypes.length (comma record) = 1 /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (time_stamp record) ++
      encode_bytes 1 (comma record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (time_stamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (comma_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_type_value, bytes) =>
                  Some ({| time_stamp := time_stamp_value; comma := comma_value; message_type := message_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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

  End MessageHeader.

  Module NewOrderAcceptedMessage.

    (** New order accepted. *)
    Record t := {
      source : list byte;
      separator_1 : N;
      user : list byte;
      separator_2 : N;
      token : list byte;
      separator_3 : N;
      buy_sell : list byte;
      separator_4 : N;
      shares : list byte;
      separator_5 : N;
      stock : list byte;
      separator_6 : N;
      price : list byte;
      separator_7 : N;
      firm : list byte;
      separator_8 : N;
      reference : list byte;
      separator_9 : N;
      time_in_force : list byte;
      separator_10 : N;
      capacity : list byte;
      separator_11 : N;
      liquidity_code : list byte;
      separator_12 : N;
      clearing_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (source record) = 6 /\
      (separator_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user record) = 4 /\
      (separator_2 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (token record) = 10 /\
      (separator_3 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_sell record) = 1 /\
      (separator_4 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (shares record) = 9 /\
      (separator_5 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock record) = 6 /\
      (separator_6 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price record) = 20 /\
      (separator_7 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm record) = 4 /\
      (separator_8 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference record) = 9 /\
      (separator_9 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (time_in_force record) = 9 /\
      (separator_10 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (capacity record) = 1 /\
      (separator_11 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (liquidity_code record) = 1 /\
      (separator_12 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (source record) ++
      encode_uint 1 (separator_1 record) ++
      encode_bytes 4 (user record) ++
      encode_uint 1 (separator_2 record) ++
      encode_bytes 10 (token record) ++
      encode_uint 1 (separator_3 record) ++
      encode_bytes 1 (buy_sell record) ++
      encode_uint 1 (separator_4 record) ++
      encode_bytes 9 (shares record) ++
      encode_uint 1 (separator_5 record) ++
      encode_bytes 6 (stock record) ++
      encode_uint 1 (separator_6 record) ++
      encode_bytes 20 (price record) ++
      encode_uint 1 (separator_7 record) ++
      encode_bytes 4 (firm record) ++
      encode_uint 1 (separator_8 record) ++
      encode_bytes 9 (reference record) ++
      encode_uint 1 (separator_9 record) ++
      encode_bytes 9 (time_in_force record) ++
      encode_uint 1 (separator_10 record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 1 (separator_11 record) ++
      encode_bytes 1 (liquidity_code record) ++
      encode_uint 1 (separator_12 record) ++
      encode_bytes 1 (clearing_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (source_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (separator_1_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (user_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (separator_2_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (token_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (separator_3_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (buy_sell_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (separator_4_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (shares_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (separator_5_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (stock_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (separator_6_value, bytes) =>
                                                      match decode_bytes 20 bytes with
                                                      | None => None
                                                      | Some (price_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (separator_7_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (firm_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (separator_8_value, bytes) =>
                                                                      match decode_bytes 9 bytes with
                                                                      | None => None
                                                                      | Some (reference_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (separator_9_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (time_in_force_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (separator_10_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (capacity_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (separator_11_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (liquidity_code_value, bytes) =>
                                                                                                  match decode_uint 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (separator_12_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (clearing_code_value, bytes) =>
                                                                                                          Some ({| source := source_value; separator_1 := separator_1_value; user := user_value; separator_2 := separator_2_value; token := token_value; separator_3 := separator_3_value; buy_sell := buy_sell_value; separator_4 := separator_4_value; shares := shares_value; separator_5 := separator_5_value; stock := stock_value; separator_6 := separator_6_value; price := price_value; separator_7 := separator_7_value; firm := firm_value; separator_8 := separator_8_value; reference := reference_value; separator_9 := separator_9_value; time_in_force := time_in_force_value; separator_10 := separator_10_value; capacity := capacity_value; separator_11 := separator_11_value; liquidity_code := liquidity_code_value; separator_12 := separator_12_value; clearing_code := clearing_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 93.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderAcceptedMessage.

  Module ExistingOrderExecutedMessage.

    (** Existing order executed. *)
    Record t := {
      source : list byte;
      separator_1 : N;
      user : list byte;
      separator_2 : N;
      token : list byte;
      separator_3 : N;
      buy_sell : list byte;
      separator_4 : N;
      shares : list byte;
      separator_5 : N;
      stock : list byte;
      separator_6 : N;
      price : list byte;
      separator_7 : N;
      firm : list byte;
      separator_8 : N;
      reference : list byte;
      separator_9 : N;
      match_number : list byte;
      separator_10 : N;
      capacity : list byte;
      separator_11 : N;
      liquidity_code : list byte;
      separator_12 : N;
      clearing_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (source record) = 6 /\
      (separator_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user record) = 4 /\
      (separator_2 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (token record) = 10 /\
      (separator_3 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_sell record) = 1 /\
      (separator_4 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (shares record) = 9 /\
      (separator_5 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock record) = 6 /\
      (separator_6 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price record) = 20 /\
      (separator_7 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm record) = 4 /\
      (separator_8 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference record) = 9 /\
      (separator_9 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (match_number record) = 9 /\
      (separator_10 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (capacity record) = 1 /\
      (separator_11 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (liquidity_code record) = 1 /\
      (separator_12 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (source record) ++
      encode_uint 1 (separator_1 record) ++
      encode_bytes 4 (user record) ++
      encode_uint 1 (separator_2 record) ++
      encode_bytes 10 (token record) ++
      encode_uint 1 (separator_3 record) ++
      encode_bytes 1 (buy_sell record) ++
      encode_uint 1 (separator_4 record) ++
      encode_bytes 9 (shares record) ++
      encode_uint 1 (separator_5 record) ++
      encode_bytes 6 (stock record) ++
      encode_uint 1 (separator_6 record) ++
      encode_bytes 20 (price record) ++
      encode_uint 1 (separator_7 record) ++
      encode_bytes 4 (firm record) ++
      encode_uint 1 (separator_8 record) ++
      encode_bytes 9 (reference record) ++
      encode_uint 1 (separator_9 record) ++
      encode_bytes 9 (match_number record) ++
      encode_uint 1 (separator_10 record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 1 (separator_11 record) ++
      encode_bytes 1 (liquidity_code record) ++
      encode_uint 1 (separator_12 record) ++
      encode_bytes 1 (clearing_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (source_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (separator_1_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (user_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (separator_2_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (token_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (separator_3_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (buy_sell_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (separator_4_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (shares_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (separator_5_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (stock_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (separator_6_value, bytes) =>
                                                      match decode_bytes 20 bytes with
                                                      | None => None
                                                      | Some (price_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (separator_7_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (firm_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (separator_8_value, bytes) =>
                                                                      match decode_bytes 9 bytes with
                                                                      | None => None
                                                                      | Some (reference_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (separator_9_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (match_number_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (separator_10_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (capacity_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (separator_11_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (liquidity_code_value, bytes) =>
                                                                                                  match decode_uint 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (separator_12_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (clearing_code_value, bytes) =>
                                                                                                          Some ({| source := source_value; separator_1 := separator_1_value; user := user_value; separator_2 := separator_2_value; token := token_value; separator_3 := separator_3_value; buy_sell := buy_sell_value; separator_4 := separator_4_value; shares := shares_value; separator_5 := separator_5_value; stock := stock_value; separator_6 := separator_6_value; price := price_value; separator_7 := separator_7_value; firm := firm_value; separator_8 := separator_8_value; reference := reference_value; separator_9 := separator_9_value; match_number := match_number_value; separator_10 := separator_10_value; capacity := capacity_value; separator_11 := separator_11_value; liquidity_code := liquidity_code_value; separator_12 := separator_12_value; clearing_code := clearing_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 93.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExistingOrderExecutedMessage.

  Module ExistingOrderCanceledMessage.

    (** Existing order canceled. *)
    Record t := {
      source : list byte;
      separator_1 : N;
      user : list byte;
      separator_2 : N;
      token : list byte;
      separator_3 : N;
      buy_sell : list byte;
      separator_4 : N;
      shares : list byte;
      separator_5 : N;
      stock : list byte;
      separator_6 : N;
      price : list byte;
      separator_7 : N;
      firm : list byte;
      separator_8 : N;
      reference : list byte;
      separator_9 : N;
      time_in_force : list byte;
      separator_10 : N;
      capacity : list byte;
      separator_11 : N;
      cancel_reason : list byte;
      separator_12 : N;
      clearing_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (source record) = 6 /\
      (separator_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user record) = 4 /\
      (separator_2 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (token record) = 10 /\
      (separator_3 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_sell record) = 1 /\
      (separator_4 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (shares record) = 9 /\
      (separator_5 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock record) = 6 /\
      (separator_6 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price record) = 20 /\
      (separator_7 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm record) = 4 /\
      (separator_8 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference record) = 9 /\
      (separator_9 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (time_in_force record) = 9 /\
      (separator_10 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (capacity record) = 1 /\
      (separator_11 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (cancel_reason record) = 1 /\
      (separator_12 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (source record) ++
      encode_uint 1 (separator_1 record) ++
      encode_bytes 4 (user record) ++
      encode_uint 1 (separator_2 record) ++
      encode_bytes 10 (token record) ++
      encode_uint 1 (separator_3 record) ++
      encode_bytes 1 (buy_sell record) ++
      encode_uint 1 (separator_4 record) ++
      encode_bytes 9 (shares record) ++
      encode_uint 1 (separator_5 record) ++
      encode_bytes 6 (stock record) ++
      encode_uint 1 (separator_6 record) ++
      encode_bytes 20 (price record) ++
      encode_uint 1 (separator_7 record) ++
      encode_bytes 4 (firm record) ++
      encode_uint 1 (separator_8 record) ++
      encode_bytes 9 (reference record) ++
      encode_uint 1 (separator_9 record) ++
      encode_bytes 9 (time_in_force record) ++
      encode_uint 1 (separator_10 record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 1 (separator_11 record) ++
      encode_bytes 1 (cancel_reason record) ++
      encode_uint 1 (separator_12 record) ++
      encode_bytes 1 (clearing_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (source_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (separator_1_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (user_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (separator_2_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (token_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (separator_3_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (buy_sell_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (separator_4_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (shares_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (separator_5_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (stock_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (separator_6_value, bytes) =>
                                                      match decode_bytes 20 bytes with
                                                      | None => None
                                                      | Some (price_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (separator_7_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (firm_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (separator_8_value, bytes) =>
                                                                      match decode_bytes 9 bytes with
                                                                      | None => None
                                                                      | Some (reference_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (separator_9_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (time_in_force_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (separator_10_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (capacity_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (separator_11_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (cancel_reason_value, bytes) =>
                                                                                                  match decode_uint 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (separator_12_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (clearing_code_value, bytes) =>
                                                                                                          Some ({| source := source_value; separator_1 := separator_1_value; user := user_value; separator_2 := separator_2_value; token := token_value; separator_3 := separator_3_value; buy_sell := buy_sell_value; separator_4 := separator_4_value; shares := shares_value; separator_5 := separator_5_value; stock := stock_value; separator_6 := separator_6_value; price := price_value; separator_7 := separator_7_value; firm := firm_value; separator_8 := separator_8_value; reference := reference_value; separator_9 := separator_9_value; time_in_force := time_in_force_value; separator_10 := separator_10_value; capacity := capacity_value; separator_11 := separator_11_value; cancel_reason := cancel_reason_value; separator_12 := separator_12_value; clearing_code := clearing_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 93.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExistingOrderCanceledMessage.

  Module PreviousExecutionBrokenMessage.

    (** Previous execution broken. *)
    Record t := {
      source : list byte;
      separator_1 : N;
      user : list byte;
      separator_2 : N;
      token : list byte;
      separator_3 : N;
      buy_sell : list byte;
      separator_4 : N;
      shares : list byte;
      separator_5 : N;
      stock : list byte;
      separator_6 : N;
      price : list byte;
      separator_7 : N;
      firm : list byte;
      separator_8 : N;
      reference : list byte;
      separator_9 : N;
      match_number : list byte;
      separator_10 : N;
      capacity : list byte;
      separator_11 : N;
      liquidity_code : list byte;
      separator_12 : N;
      clearing_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (source record) = 6 /\
      (separator_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user record) = 4 /\
      (separator_2 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (token record) = 10 /\
      (separator_3 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_sell record) = 1 /\
      (separator_4 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (shares record) = 9 /\
      (separator_5 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock record) = 6 /\
      (separator_6 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price record) = 20 /\
      (separator_7 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm record) = 4 /\
      (separator_8 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference record) = 9 /\
      (separator_9 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (match_number record) = 9 /\
      (separator_10 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (capacity record) = 1 /\
      (separator_11 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (liquidity_code record) = 1 /\
      (separator_12 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (source record) ++
      encode_uint 1 (separator_1 record) ++
      encode_bytes 4 (user record) ++
      encode_uint 1 (separator_2 record) ++
      encode_bytes 10 (token record) ++
      encode_uint 1 (separator_3 record) ++
      encode_bytes 1 (buy_sell record) ++
      encode_uint 1 (separator_4 record) ++
      encode_bytes 9 (shares record) ++
      encode_uint 1 (separator_5 record) ++
      encode_bytes 6 (stock record) ++
      encode_uint 1 (separator_6 record) ++
      encode_bytes 20 (price record) ++
      encode_uint 1 (separator_7 record) ++
      encode_bytes 4 (firm record) ++
      encode_uint 1 (separator_8 record) ++
      encode_bytes 9 (reference record) ++
      encode_uint 1 (separator_9 record) ++
      encode_bytes 9 (match_number record) ++
      encode_uint 1 (separator_10 record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 1 (separator_11 record) ++
      encode_bytes 1 (liquidity_code record) ++
      encode_uint 1 (separator_12 record) ++
      encode_bytes 1 (clearing_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (source_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (separator_1_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (user_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (separator_2_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (token_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (separator_3_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (buy_sell_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (separator_4_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (shares_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (separator_5_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (stock_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (separator_6_value, bytes) =>
                                                      match decode_bytes 20 bytes with
                                                      | None => None
                                                      | Some (price_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (separator_7_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (firm_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (separator_8_value, bytes) =>
                                                                      match decode_bytes 9 bytes with
                                                                      | None => None
                                                                      | Some (reference_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (separator_9_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (match_number_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (separator_10_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (capacity_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (separator_11_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (liquidity_code_value, bytes) =>
                                                                                                  match decode_uint 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (separator_12_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (clearing_code_value, bytes) =>
                                                                                                          Some ({| source := source_value; separator_1 := separator_1_value; user := user_value; separator_2 := separator_2_value; token := token_value; separator_3 := separator_3_value; buy_sell := buy_sell_value; separator_4 := separator_4_value; shares := shares_value; separator_5 := separator_5_value; stock := stock_value; separator_6 := separator_6_value; price := price_value; separator_7 := separator_7_value; firm := firm_value; separator_8 := separator_8_value; reference := reference_value; separator_9 := separator_9_value; match_number := match_number_value; separator_10 := separator_10_value; capacity := capacity_value; separator_11 := separator_11_value; liquidity_code := liquidity_code_value; separator_12 := separator_12_value; clearing_code := clearing_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 93.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousExecutionBrokenMessage.

End NsmEquitiesDropV10.
