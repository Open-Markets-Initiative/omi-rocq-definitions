From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The Members Exchange Risk Control

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
      - a Reassemble rule
      - the dispatch that chooses a message by its type
      - a block whose stated length holds more than its fields

    License: MIT No Attribution
  *)

Module MemxOptionsRiskControlV13Client.

  Module CommonHeader.

    (** Tcp Common Header *)
    Record t := {
      message_type : N;
      message_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_type record < 256 ^ N.of_nat 1)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_type record) ++
      encode_uint 2 (message_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_type_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_length_value, bytes) =>
              Some ({| message_type := message_type_value; message_length := message_length_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End CommonHeader.

  Module LoginRequestMessage.

    (** Memx Tcp Login message *)
    Record t := {
      token_type : list byte;
      token : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (token_type record) = 1 /\
      Datatypes.length (token record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (token_type record) ++
      encode_bytes 1 (token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (token_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (token_value, bytes) =>
              Some ({| token_type := token_type_value; token := token_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End LoginRequestMessage.

  Module ReplayRequestMessage.

    (** Memx Tcp Replay Request message *)
    Record t := {
      session_id : N;
      next_sequence_number : N;
      count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 8)%N /\
      (next_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (session_id record) ++
      encode_uint 8 (next_sequence_number record) ++
      encode_uint 4 (count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (next_sequence_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (count_value, bytes) =>
                  Some ({| session_id := session_id_value; next_sequence_number := next_sequence_number_value; count := count_value |}, bytes)
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

  End ReplayRequestMessage.

  Module ReplayAllRequestMessage.

    (** Memx Tcp Replay All Request message *)
    Record t := {
      session_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          Some ({| session_id := session_id_value |}, bytes)
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

  End ReplayAllRequestMessage.

  Module StreamRequestMessage.

    (** Memx Tcp Stream Request message *)
    Record t := {
      session_id : N;
      next_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 8)%N /\
      (next_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (session_id record) ++
      encode_uint 8 (next_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (next_sequence_number_value, bytes) =>
              Some ({| session_id := session_id_value; next_sequence_number := next_sequence_number_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End StreamRequestMessage.

  Module SbeHeader.

    (** Sbe Header *)
    Record t := {
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 1)%N /\
      (schema_id record < 256 ^ N.of_nat 1)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 1 (template_id record) ++
      encode_uint 1 (schema_id record) ++
      encode_uint 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (version_value, bytes) =>
                      Some ({| block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value |}, bytes)
                  end
              end
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

  End SbeHeader.

  Module RiskSettingsQueryMessage.

    (** RiskSettingsQueryMessage *)
    Record t := {
      cl_ord_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          Some ({| cl_ord_id := cl_ord_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End RiskSettingsQueryMessage.

  Module ActiveRiskThresholdChangeReqMessage.

    (** ActiveRiskThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_active_risk_threshold_change_req_underlier : list byte;
      efid_active_risk_threshold_change_req_efid : list byte;
      threshold_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_active_risk_threshold_change_req_underlier record) = 6 /\
      Datatypes.length (efid_active_risk_threshold_change_req_efid record) = 4 /\
      (threshold_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_active_risk_threshold_change_req_underlier record) ++
      encode_bytes 4 (efid_active_risk_threshold_change_req_efid record) ++
      encode_uint 4 (threshold_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_active_risk_threshold_change_req_underlier_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_active_risk_threshold_change_req_efid_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (threshold_quantity_value, bytes) =>
                      Some ({| cl_ord_id := cl_ord_id_value; underlier_active_risk_threshold_change_req_underlier := underlier_active_risk_threshold_change_req_underlier_value; efid_active_risk_threshold_change_req_efid := efid_active_risk_threshold_change_req_efid_value; threshold_quantity := threshold_quantity_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
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

  End ActiveRiskThresholdChangeReqMessage.

  Module ActiveRiskAcknowledgementReqMessage.

    (** ActiveRiskAcknowledgementReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier : list byte;
      efid : list byte;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier record) = 6 /\
      Datatypes.length (efid record) = 4 /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier record) ++
      encode_bytes 4 (efid record) ++
      encode_uint 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      Some ({| cl_ord_id := cl_ord_id_value; underlier := underlier_value; efid := efid_value; quantity := quantity_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
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

  End ActiveRiskAcknowledgementReqMessage.

  Module CpVolumeThresholdChangeReqMessage.

    (** CPVolumeThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      volume : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (volume record < 256 ^ N.of_nat 8)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 8 (volume record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (volume_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (period_in_milli_seconds_value, bytes) =>
                              Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; volume := volume_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpVolumeThresholdChangeReqMessage.

  Module CpExecutedNotionalThresholdChangeReqMessage.

    (** CPExecutedNotionalThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      price_in_dollars : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (price_in_dollars record < 256 ^ N.of_nat 4)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (price_in_dollars record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_in_dollars_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (period_in_milli_seconds_value, bytes) =>
                              Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; price_in_dollars := price_in_dollars_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpExecutedNotionalThresholdChangeReqMessage.

  Module CpTotalExecutionsThresholdChangeReqMessage.

    (** CPTotalExecutionsThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      total_executions : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (total_executions record < 256 ^ N.of_nat 4)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (total_executions record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (total_executions_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (period_in_milli_seconds_value, bytes) =>
                              Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; total_executions := total_executions_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpTotalExecutionsThresholdChangeReqMessage.

  Module CpPercentOutstandingContractsThresholdChangeReqMessage.

    (** CPPercentOutstandingContractsThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      percent : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (percent record < 256 ^ N.of_nat 4)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 4 (percent record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (percent_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (period_in_milli_seconds_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; percent := percent_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpPercentOutstandingContractsThresholdChangeReqMessage.

  Module CpBreachCountThresholdChangeReqMessage.

    (** CPBreachCountThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      count : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (count record < 256 ^ N.of_nat 4)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (count record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (count_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (period_in_milli_seconds_value, bytes) =>
                              Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; count := count_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpBreachCountThresholdChangeReqMessage.

  Module ManualCpBreachTriggerReqMessage.

    (** ManualCPBreachTriggerReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      send_cancels : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (send_cancels record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 1 (send_cancels record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (send_cancels_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; send_cancels := send_cancels_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ManualCpBreachTriggerReqMessage.

  Module CpClearBreachReqMessage.

    (** CPClearBreachReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      breach_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      (breach_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (breach_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (breach_id_value, bytes) =>
              Some ({| cl_ord_id := cl_ord_id_value; breach_id := breach_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpClearBreachReqMessage.

  Module SingleOrderAllowIsoOrdersChangeReqMessage.

    (** SingleOrderAllowISOOrdersChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      allow_iso_orders : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (allow_iso_orders record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 1 (allow_iso_orders record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (allow_iso_orders_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; allow_iso_orders := allow_iso_orders_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleOrderAllowIsoOrdersChangeReqMessage.

  Module SingleOrderAllowOrdersInCrossedMarketChangeReqMessage.

    (** SingleOrderAllowOrdersInCrossedMarketChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      allow_orders : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (allow_orders record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 1 (allow_orders record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (allow_orders_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; allow_orders := allow_orders_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleOrderAllowOrdersInCrossedMarketChangeReqMessage.

  Module SingleOrderMaxNotionalChangeReqMessage.

    (** SingleOrderMaxNotionalChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      max_notional_in_dollars : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (max_notional_in_dollars record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (max_notional_in_dollars record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (max_notional_in_dollars_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; max_notional_in_dollars := max_notional_in_dollars_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleOrderMaxNotionalChangeReqMessage.

  Module SingleOrderMaxContractsChangeReqMessage.

    (** SingleOrderMaxContractsChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      max_contracts : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (max_contracts record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (max_contracts record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (max_contracts_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; max_contracts := max_contracts_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleOrderMaxContractsChangeReqMessage.

  Module CpGrossNotionalThresholdChangeReqMessage.

    (** CPGrossNotionalThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      price_in_dollars : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (price_in_dollars record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (price_in_dollars record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_in_dollars_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; price_in_dollars := price_in_dollars_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpGrossNotionalThresholdChangeReqMessage.

  Module CpMarketOrderGrossNotionalThresholdChangeReqMessage.

    (** CPMarketOrderGrossNotionalThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      price_in_dollars : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (price_in_dollars record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (price_in_dollars record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_in_dollars_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; price_in_dollars := price_in_dollars_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpMarketOrderGrossNotionalThresholdChangeReqMessage.

  Module CpNetNotionalThresholdChangeReqMessage.

    (** CPNetNotionalThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      price_in_dollars : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (price_in_dollars record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (price_in_dollars record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_in_dollars_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; price_in_dollars := price_in_dollars_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpNetNotionalThresholdChangeReqMessage.

  Module CpMarketOrderNetNotionalThresholdChangeReqMessage.

    (** CPMarketOrderNetNotionalThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      price_in_dollars : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (price_in_dollars record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (price_in_dollars record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_in_dollars_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; price_in_dollars := price_in_dollars_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpMarketOrderNetNotionalThresholdChangeReqMessage.

  Module CpDuplicateOrderThresholdChangeReqMessage.

    (** CPDuplicateOrderThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      max_dup_orders : N;
      use_order_price_in_dup_check_optional : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (max_dup_orders record < 256 ^ N.of_nat 4)%N /\
      (use_order_price_in_dup_check_optional record < 256 ^ N.of_nat 1)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (max_dup_orders record) ++
      encode_uint 1 (use_order_price_in_dup_check_optional record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (max_dup_orders_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (use_order_price_in_dup_check_optional_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (period_in_milli_seconds_value, bytes) =>
                                  Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; max_dup_orders := max_dup_orders_value; use_order_price_in_dup_check_optional := use_order_price_in_dup_check_optional_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpDuplicateOrderThresholdChangeReqMessage.

  Module CpOrderRateThresholdChangeReqMessage.

    (** CPOrderRateThresholdChangeReqMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      max_order_msgs : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (max_order_msgs record < 256 ^ N.of_nat 4)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (max_order_msgs record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (max_order_msgs_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (period_in_milli_seconds_value, bytes) =>
                              Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; max_order_msgs := max_order_msgs_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpOrderRateThresholdChangeReqMessage.

End MemxOptionsRiskControlV13Client.
