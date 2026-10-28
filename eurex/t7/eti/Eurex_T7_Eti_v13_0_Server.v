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

Module EurexT7EtiV130Server.

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

  Module NrResponseHeaderMeComp.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp.

  Module NrResponseHeaderMeComp2.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp2.

  Module NrResponseHeaderMeComp3.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp3.

  Module RbcHeaderComp.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp.

  Module RbcHeaderComp2.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp2.

  Module RbcHeaderComp3.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp3.

  Module RbcHeaderComp4.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp4.

  Module ResponseHeaderComp.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp.

  Module RbcHeaderComp5.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp5.

  Module OldBasketDataBcGrpComp.

    Record t := {
      transact_time : N;
      basket_trd_match_id : N;
      orig_basket_trd_match_id : N;
      trade_report_id : list byte;
      maturity_month_year : N;
      optional_early_termination_indicator : N;
      basket_trade_report_type : N;
      basket_trade_report_text : list byte;
      pad2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (basket_trd_match_id record < 256 ^ N.of_nat 8)%N /\
      (orig_basket_trd_match_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_report_id record) = 20 /\
      (maturity_month_year record < 256 ^ N.of_nat 4)%N /\
      (optional_early_termination_indicator record < 256 ^ N.of_nat 1)%N /\
      (basket_trade_report_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (basket_trade_report_text record) = 20 /\
      (pad2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (basket_trd_match_id record) ++
      encode_uint 8 (orig_basket_trd_match_id record) ++
      encode_bytes 20 (trade_report_id record) ++
      encode_uint 4 (maturity_month_year record) ++
      encode_uint 1 (optional_early_termination_indicator record) ++
      encode_uint 1 (basket_trade_report_type record) ++
      encode_bytes 20 (basket_trade_report_text record) ++
      encode_uint 2 (pad2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (basket_trd_match_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (orig_basket_trd_match_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (trade_report_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (maturity_month_year_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (optional_early_termination_indicator_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (basket_trade_report_type_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (basket_trade_report_text_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (pad2_value, bytes) =>
                                          Some ({| transact_time := transact_time_value; basket_trd_match_id := basket_trd_match_id_value; orig_basket_trd_match_id := orig_basket_trd_match_id_value; trade_report_id := trade_report_id_value; maturity_month_year := maturity_month_year_value; optional_early_termination_indicator := optional_early_termination_indicator_value; basket_trade_report_type := basket_trade_report_type_value; basket_trade_report_text := basket_trade_report_text_value; pad2 := pad2_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OldBasketDataBcGrpComp.

  Module NewBasketDataBcGrpComp.

    Record t := {
      transact_time : N;
      basket_trd_match_id : N;
      orig_basket_trd_match_id : N;
      trade_report_id : list byte;
      maturity_month_year : N;
      optional_early_termination_indicator : N;
      basket_trade_report_type : N;
      basket_trade_report_text : list byte;
      pad2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (basket_trd_match_id record < 256 ^ N.of_nat 8)%N /\
      (orig_basket_trd_match_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_report_id record) = 20 /\
      (maturity_month_year record < 256 ^ N.of_nat 4)%N /\
      (optional_early_termination_indicator record < 256 ^ N.of_nat 1)%N /\
      (basket_trade_report_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (basket_trade_report_text record) = 20 /\
      (pad2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (basket_trd_match_id record) ++
      encode_uint 8 (orig_basket_trd_match_id record) ++
      encode_bytes 20 (trade_report_id record) ++
      encode_uint 4 (maturity_month_year record) ++
      encode_uint 1 (optional_early_termination_indicator record) ++
      encode_uint 1 (basket_trade_report_type record) ++
      encode_bytes 20 (basket_trade_report_text record) ++
      encode_uint 2 (pad2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (basket_trd_match_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (orig_basket_trd_match_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (trade_report_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (maturity_month_year_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (optional_early_termination_indicator_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (basket_trade_report_type_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (basket_trade_report_text_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (pad2_value, bytes) =>
                                          Some ({| transact_time := transact_time_value; basket_trd_match_id := basket_trd_match_id_value; orig_basket_trd_match_id := orig_basket_trd_match_id_value; trade_report_id := trade_report_id_value; maturity_month_year := maturity_month_year_value; optional_early_termination_indicator := optional_early_termination_indicator_value; basket_trade_report_type := basket_trade_report_type_value; basket_trade_report_text := basket_trade_report_text_value; pad2 := pad2_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewBasketDataBcGrpComp.

  Module NotifHeaderComp.

    Record t := {
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          Some ({| sending_time := sending_time_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NotifHeaderComp.

  Module RbcHeaderMeComp.

    Record t := {
      trd_reg_ts_time_out : N;
      notification_in : N;
      sending_time : N;
      appl_sub_id : N;
      partition_id : N;
      appl_msg_id : list byte;
      appl_id : N;
      appl_resend_flag : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (notification_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (notification_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_out_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (notification_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (appl_sub_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (partition_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (appl_msg_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (appl_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_resend_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (last_fragment_value, bytes) =>
                                          match decode_uint 7 bytes with
                                          | None => None
                                          | Some (pad7_value, bytes) =>
                                              Some ({| trd_reg_ts_time_out := trd_reg_ts_time_out_value; notification_in := notification_in_value; sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_msg_id := appl_msg_id_value; appl_id := appl_id_value; appl_resend_flag := appl_resend_flag_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RbcHeaderMeComp.

  Module RbcHeaderMeComp2.

    Record t := {
      trd_reg_ts_time_out : N;
      notification_in : N;
      sending_time : N;
      appl_sub_id : N;
      partition_id : N;
      appl_msg_id : list byte;
      appl_id : N;
      appl_resend_flag : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (notification_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (notification_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_out_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (notification_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (appl_sub_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (partition_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (appl_msg_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (appl_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_resend_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (last_fragment_value, bytes) =>
                                          match decode_uint 7 bytes with
                                          | None => None
                                          | Some (pad7_value, bytes) =>
                                              Some ({| trd_reg_ts_time_out := trd_reg_ts_time_out_value; notification_in := notification_in_value; sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_msg_id := appl_msg_id_value; appl_id := appl_id_value; appl_resend_flag := appl_resend_flag_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RbcHeaderMeComp2.

  Module NrResponseHeaderMeComp4.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp4.

  Module NrResponseHeaderMeComp5.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp5.

  Module RbcHeaderMeComp3.

    Record t := {
      trd_reg_ts_time_out : N;
      notification_in : N;
      sending_time : N;
      appl_sub_id : N;
      partition_id : N;
      appl_msg_id : list byte;
      appl_id : N;
      appl_resend_flag : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (notification_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (notification_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_out_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (notification_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (appl_sub_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (partition_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (appl_msg_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (appl_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_resend_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (last_fragment_value, bytes) =>
                                          match decode_uint 7 bytes with
                                          | None => None
                                          | Some (pad7_value, bytes) =>
                                              Some ({| trd_reg_ts_time_out := trd_reg_ts_time_out_value; notification_in := notification_in_value; sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_msg_id := appl_msg_id_value; appl_id := appl_id_value; appl_resend_flag := appl_resend_flag_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RbcHeaderMeComp3.

  Module NrResponseHeaderMeComp6.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp6.

  Module RbcHeaderMeComp4.

    Record t := {
      trd_reg_ts_time_out : N;
      notification_in : N;
      sending_time : N;
      appl_sub_id : N;
      partition_id : N;
      appl_msg_id : list byte;
      appl_id : N;
      appl_resend_flag : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (notification_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (notification_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_out_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (notification_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (appl_sub_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (partition_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (appl_msg_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (appl_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_resend_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (last_fragment_value, bytes) =>
                                          match decode_uint 7 bytes with
                                          | None => None
                                          | Some (pad7_value, bytes) =>
                                              Some ({| trd_reg_ts_time_out := trd_reg_ts_time_out_value; notification_in := notification_in_value; sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_msg_id := appl_msg_id_value; appl_id := appl_id_value; appl_resend_flag := appl_resend_flag_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RbcHeaderMeComp4.

  Module ResponseHeaderMeComp.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      partition_id : N;
      appl_id : N;
      appl_msg_id : list byte;
      last_fragment : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (last_fragment record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (last_fragment record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (partition_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_id_value, bytes) =>
                                      match decode_bytes 16 bytes with
                                      | None => None
                                      | Some (appl_msg_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (last_fragment_value, bytes) =>
                                              Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; partition_id := partition_id_value; appl_id := appl_id_value; appl_msg_id := appl_msg_id_value; last_fragment := last_fragment_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResponseHeaderMeComp.

  Module RbcHeaderMeComp5.

    Record t := {
      trd_reg_ts_time_out : N;
      notification_in : N;
      sending_time : N;
      appl_sub_id : N;
      partition_id : N;
      appl_msg_id : list byte;
      appl_id : N;
      appl_resend_flag : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (notification_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (notification_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_out_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (notification_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (appl_sub_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (partition_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (appl_msg_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (appl_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_resend_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (last_fragment_value, bytes) =>
                                          match decode_uint 7 bytes with
                                          | None => None
                                          | Some (pad7_value, bytes) =>
                                              Some ({| trd_reg_ts_time_out := trd_reg_ts_time_out_value; notification_in := notification_in_value; sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_msg_id := appl_msg_id_value; appl_id := appl_id_value; appl_resend_flag := appl_resend_flag_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RbcHeaderMeComp5.

  Module NrResponseHeaderMeComp7.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp7.

  Module RbcHeaderMeComp6.

    Record t := {
      trd_reg_ts_time_out : N;
      notification_in : N;
      sending_time : N;
      appl_sub_id : N;
      partition_id : N;
      appl_msg_id : list byte;
      appl_id : N;
      appl_resend_flag : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (notification_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (notification_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_out_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (notification_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (appl_sub_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (partition_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (appl_msg_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (appl_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_resend_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (last_fragment_value, bytes) =>
                                          match decode_uint 7 bytes with
                                          | None => None
                                          | Some (pad7_value, bytes) =>
                                              Some ({| trd_reg_ts_time_out := trd_reg_ts_time_out_value; notification_in := notification_in_value; sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_msg_id := appl_msg_id_value; appl_id := appl_id_value; appl_resend_flag := appl_resend_flag_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RbcHeaderMeComp6.

  Module NrResponseHeaderMeComp8.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp8.

  Module ResponseHeaderMeComp2.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      partition_id : N;
      appl_id : N;
      appl_msg_id : list byte;
      last_fragment : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (last_fragment record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (last_fragment record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (partition_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_id_value, bytes) =>
                                      match decode_bytes 16 bytes with
                                      | None => None
                                      | Some (appl_msg_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (last_fragment_value, bytes) =>
                                              Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; partition_id := partition_id_value; appl_id := appl_id_value; appl_msg_id := appl_msg_id_value; last_fragment := last_fragment_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResponseHeaderMeComp2.

  Module NotifHeaderComp2.

    Record t := {
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          Some ({| sending_time := sending_time_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NotifHeaderComp2.

  Module NotifHeaderComp3.

    Record t := {
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          Some ({| sending_time := sending_time_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NotifHeaderComp3.

  Module NotifHeaderComp4.

    Record t := {
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          Some ({| sending_time := sending_time_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NotifHeaderComp4.

  Module ResponseHeaderComp2.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp2.

  Module NrResponseHeaderMeComp9.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp9.

  Module NrResponseHeaderMeComp10.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp10.

  Module ResponseHeaderComp3.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp3.

  Module ResponseHeaderComp4.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp4.

  Module RbcHeaderComp6.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp6.

  Module ResponseHeaderComp5.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp5.

  Module ResponseHeaderComp6.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp6.

  Module NrResponseHeaderMeComp11.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp11.

  Module NrResponseHeaderMeComp12.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp12.

  Module NrResponseHeaderMeComp13.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp13.

  Module NrResponseHeaderMeComp14.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp14.

  Module ResponseHeaderMeComp3.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      partition_id : N;
      appl_id : N;
      appl_msg_id : list byte;
      last_fragment : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (last_fragment record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (last_fragment record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (partition_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_id_value, bytes) =>
                                      match decode_bytes 16 bytes with
                                      | None => None
                                      | Some (appl_msg_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (last_fragment_value, bytes) =>
                                              Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; partition_id := partition_id_value; appl_id := appl_id_value; appl_msg_id := appl_msg_id_value; last_fragment := last_fragment_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResponseHeaderMeComp3.

  Module NrResponseHeaderMeComp15.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp15.

  Module ResponseHeaderMeComp4.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      partition_id : N;
      appl_id : N;
      appl_msg_id : list byte;
      last_fragment : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (last_fragment record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (last_fragment record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (partition_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_id_value, bytes) =>
                                      match decode_bytes 16 bytes with
                                      | None => None
                                      | Some (appl_msg_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (last_fragment_value, bytes) =>
                                              Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; partition_id := partition_id_value; appl_id := appl_id_value; appl_msg_id := appl_msg_id_value; last_fragment := last_fragment_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResponseHeaderMeComp4.

  Module RbcHeaderComp7.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp7.

  Module RbcHeaderMeComp7.

    Record t := {
      trd_reg_ts_time_out : N;
      notification_in : N;
      sending_time : N;
      appl_sub_id : N;
      partition_id : N;
      appl_msg_id : list byte;
      appl_id : N;
      appl_resend_flag : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (notification_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (notification_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_out_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (notification_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (appl_sub_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (partition_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (appl_msg_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (appl_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_resend_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (last_fragment_value, bytes) =>
                                          match decode_uint 7 bytes with
                                          | None => None
                                          | Some (pad7_value, bytes) =>
                                              Some ({| trd_reg_ts_time_out := trd_reg_ts_time_out_value; notification_in := notification_in_value; sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_msg_id := appl_msg_id_value; appl_id := appl_id_value; appl_resend_flag := appl_resend_flag_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RbcHeaderMeComp7.

  Module RbcHeaderMeComp8.

    Record t := {
      trd_reg_ts_time_out : N;
      notification_in : N;
      sending_time : N;
      appl_sub_id : N;
      partition_id : N;
      appl_msg_id : list byte;
      appl_id : N;
      appl_resend_flag : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (notification_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (notification_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_out_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (notification_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (appl_sub_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (partition_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (appl_msg_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (appl_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_resend_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (last_fragment_value, bytes) =>
                                          match decode_uint 7 bytes with
                                          | None => None
                                          | Some (pad7_value, bytes) =>
                                              Some ({| trd_reg_ts_time_out := trd_reg_ts_time_out_value; notification_in := notification_in_value; sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_msg_id := appl_msg_id_value; appl_id := appl_id_value; appl_resend_flag := appl_resend_flag_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RbcHeaderMeComp8.

  Module ResponseHeaderMeComp5.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      partition_id : N;
      appl_id : N;
      appl_msg_id : list byte;
      last_fragment : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (last_fragment record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (last_fragment record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (partition_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_id_value, bytes) =>
                                      match decode_bytes 16 bytes with
                                      | None => None
                                      | Some (appl_msg_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (last_fragment_value, bytes) =>
                                              Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; partition_id := partition_id_value; appl_id := appl_id_value; appl_msg_id := appl_msg_id_value; last_fragment := last_fragment_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResponseHeaderMeComp5.

  Module RbcHeaderComp8.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp8.

  Module RbcHeaderComp9.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp9.

  Module NrResponseHeaderMeComp16.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp16.

  Module NrResponseHeaderMeComp17.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp17.

  Module RbcHeaderMeComp9.

    Record t := {
      trd_reg_ts_time_out : N;
      notification_in : N;
      sending_time : N;
      appl_sub_id : N;
      partition_id : N;
      appl_msg_id : list byte;
      appl_id : N;
      appl_resend_flag : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (notification_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (notification_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_out_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (notification_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (appl_sub_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (partition_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (appl_msg_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (appl_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_resend_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (last_fragment_value, bytes) =>
                                          match decode_uint 7 bytes with
                                          | None => None
                                          | Some (pad7_value, bytes) =>
                                              Some ({| trd_reg_ts_time_out := trd_reg_ts_time_out_value; notification_in := notification_in_value; sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_msg_id := appl_msg_id_value; appl_id := appl_id_value; appl_resend_flag := appl_resend_flag_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RbcHeaderMeComp9.

  Module NrResponseHeaderMeComp18.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp18.

  Module RbcHeaderMeComp10.

    Record t := {
      trd_reg_ts_time_out : N;
      notification_in : N;
      sending_time : N;
      appl_sub_id : N;
      partition_id : N;
      appl_msg_id : list byte;
      appl_id : N;
      appl_resend_flag : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (notification_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (notification_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_out_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (notification_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (appl_sub_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (partition_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (appl_msg_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (appl_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_resend_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (last_fragment_value, bytes) =>
                                          match decode_uint 7 bytes with
                                          | None => None
                                          | Some (pad7_value, bytes) =>
                                              Some ({| trd_reg_ts_time_out := trd_reg_ts_time_out_value; notification_in := notification_in_value; sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_msg_id := appl_msg_id_value; appl_id := appl_id_value; appl_resend_flag := appl_resend_flag_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RbcHeaderMeComp10.

  Module NrResponseHeaderMeComp19.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp19.

  Module NrResponseHeaderMeComp20.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp20.

  Module ResponseHeaderComp7.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp7.

  Module ResponseHeaderComp8.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp8.

  Module RbcHeaderComp10.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp10.

  Module RbcHeaderComp11.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp11.

  Module RbcHeaderComp12.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp12.

  Module ResponseHeaderComp9.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp9.

  Module ResponseHeaderComp10.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp10.

  Module RbcHeaderComp13.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp13.

  Module RbcHeaderComp14.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp14.

  Module RbcHeaderComp15.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp15.

  Module RbcHeaderComp16.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp16.

  Module RbcHeaderComp17.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp17.

  Module RbcHeaderComp18.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp18.

  Module ResponseHeaderComp11.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp11.

  Module RbcHeaderComp19.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp19.

  Module ResponseHeaderComp12.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp12.

  Module RbcHeaderComp20.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp20.

  Module NrbcHeaderComp.

    Record t := {
      sending_time : N;
      appl_sub_id : N;
      appl_id : N;
      last_fragment : N;
      pad2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 2 (pad2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (appl_sub_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (last_fragment_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (pad2_value, bytes) =>
                          Some ({| sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad2 := pad2_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End NrbcHeaderComp.

  Module NrbcHeaderComp2.

    Record t := {
      sending_time : N;
      appl_sub_id : N;
      appl_id : N;
      last_fragment : N;
      pad2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 2 (pad2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (appl_sub_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (last_fragment_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (pad2_value, bytes) =>
                          Some ({| sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad2 := pad2_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End NrbcHeaderComp2.

  Module RbcHeaderComp21.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp21.

  Module ResponseHeaderComp13.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp13.

  Module RbcHeaderComp22.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp22.

  Module RbcHeaderComp23.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp23.

  Module RbcHeaderComp24.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp24.

  Module RbcHeaderComp25.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp25.

  Module ResponseHeaderComp14.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp14.

  Module RbcHeaderComp26.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp26.

  Module RbcHeaderComp27.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp27.

  Module RbcHeaderComp28.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp28.

  Module RbcHeaderComp29.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp29.

  Module RbcHeaderComp30.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp30.

  Module NotifHeaderComp5.

    Record t := {
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          Some ({| sending_time := sending_time_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NotifHeaderComp5.

  Module RbcHeaderComp31.

    Record t := {
      sending_time : N;
      appl_seq_num : N;
      appl_sub_id : N;
      partition_id : N;
      appl_resend_flag : N;
      appl_id : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (appl_sub_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appl_resend_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (pad7_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; appl_seq_num := appl_seq_num_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_resend_flag := appl_resend_flag_value; appl_id := appl_id_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RbcHeaderComp31.

  Module RbcHeaderMeComp11.

    Record t := {
      trd_reg_ts_time_out : N;
      notification_in : N;
      sending_time : N;
      appl_sub_id : N;
      partition_id : N;
      appl_msg_id : list byte;
      appl_id : N;
      appl_resend_flag : N;
      last_fragment : N;
      pad7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (notification_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (appl_sub_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_msg_id record) = 16 /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (appl_resend_flag record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (notification_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (appl_sub_id record) ++
      encode_uint 2 (partition_id record) ++
      encode_bytes 16 (appl_msg_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (appl_resend_flag record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 7 (pad7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_out_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (notification_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (appl_sub_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (partition_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (appl_msg_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (appl_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (appl_resend_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (last_fragment_value, bytes) =>
                                          match decode_uint 7 bytes with
                                          | None => None
                                          | Some (pad7_value, bytes) =>
                                              Some ({| trd_reg_ts_time_out := trd_reg_ts_time_out_value; notification_in := notification_in_value; sending_time := sending_time_value; appl_sub_id := appl_sub_id_value; partition_id := partition_id_value; appl_msg_id := appl_msg_id_value; appl_id := appl_id_value; appl_resend_flag := appl_resend_flag_value; last_fragment := last_fragment_value; pad7 := pad7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RbcHeaderMeComp11.

  Module ResponseHeaderComp15.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp15.

  Module NrResponseHeaderMeComp21.

    Record t := {
      request_time : N;
      trd_reg_ts_time_in : N;
      trd_reg_ts_time_out : N;
      response_in : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_out record < 256 ^ N.of_nat 8)%N /\
      (response_in record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_time_out record) ++
      encode_uint 8 (response_in record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 1 (last_fragment record) ++
      encode_uint 3 (pad3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_time_in_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trd_reg_ts_time_out_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (response_in_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (msg_seq_num_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (last_fragment_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (pad3_value, bytes) =>
                                      Some ({| request_time := request_time_value; trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_time_out := trd_reg_ts_time_out_value; response_in := response_in_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NrResponseHeaderMeComp21.

  Module ResponseHeaderComp16.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp16.

  Module ResponseHeaderComp17.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (request_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; pad4 := pad4_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResponseHeaderComp17.

End EurexT7EtiV130Server.
