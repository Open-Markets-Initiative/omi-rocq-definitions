From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Eurex Exchange Extended Derivatives Clearing Interface

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

Module EurexT7EdciV130Server.

  Module MessageHeader.

    (** Eurex T7 Edci message header *)
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

  Module RbcHeaderComp.

    Record t := {
      sending_time : N;
      party_id_executing_unit : N;
      partition_id : N;
      appl_id : N;
      last_fragment : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (party_id_executing_unit record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (party_id_executing_unit record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (party_id_executing_unit_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (partition_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (appl_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (last_fragment_value, bytes) =>
                          Some ({| sending_time := sending_time_value; party_id_executing_unit := party_id_executing_unit_value; partition_id := partition_id_value; appl_id := appl_id_value; last_fragment := last_fragment_value |}, bytes)
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

  End RbcHeaderComp.

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

  Module ResponseHeaderComp.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
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
                          Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                      end
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

  End ResponseHeaderComp.

  Module ResponseHeaderComp2.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
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
                          Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                      end
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

  End ResponseHeaderComp2.

  Module RbcHeaderComp2.

    Record t := {
      sending_time : N;
      party_id_executing_unit : N;
      partition_id : N;
      appl_id : N;
      last_fragment : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (party_id_executing_unit record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (party_id_executing_unit record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (party_id_executing_unit_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (partition_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (appl_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (last_fragment_value, bytes) =>
                          Some ({| sending_time := sending_time_value; party_id_executing_unit := party_id_executing_unit_value; partition_id := partition_id_value; appl_id := appl_id_value; last_fragment := last_fragment_value |}, bytes)
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

  End RbcHeaderComp2.

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

  Module ResponseHeaderComp3.

    Record t := {
      request_time : N;
      sending_time : N;
      msg_seq_num : N;
      last_fragment : N;
      pad3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (request_time record) ++
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
                          Some ({| request_time := request_time_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; last_fragment := last_fragment_value; pad3 := pad3_value |}, bytes)
                      end
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

  End ResponseHeaderComp3.

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

  Module RbcHeaderComp3.

    Record t := {
      sending_time : N;
      party_id_executing_unit : N;
      partition_id : N;
      appl_id : N;
      last_fragment : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (party_id_executing_unit record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 2)%N /\
      (appl_id record < 256 ^ N.of_nat 1)%N /\
      (last_fragment record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 4 (party_id_executing_unit record) ++
      encode_uint 2 (partition_id record) ++
      encode_uint 1 (appl_id record) ++
      encode_uint 1 (last_fragment record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (party_id_executing_unit_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (partition_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (appl_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (last_fragment_value, bytes) =>
                          Some ({| sending_time := sending_time_value; party_id_executing_unit := party_id_executing_unit_value; partition_id := partition_id_value; appl_id := appl_id_value; last_fragment := last_fragment_value |}, bytes)
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

  End RbcHeaderComp3.

End EurexT7EdciV130Server.
