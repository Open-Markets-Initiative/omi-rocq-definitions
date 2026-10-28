From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Eurex Exchange Enhanced Order Book Interface

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
      - a run counted by a field
  *)

Module EurexT7EobiV25.

  Module EobiHeader.

    (** EOBI PacketHeader MessageHeaderComp (BodyLen + TemplateID + MsgSeqNum) — first 8 bytes of every Eurex T7 EOBI packet. *)
    Record t := {
      body_len : N;
      template_id : N;
      msg_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (body_len record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 2)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (body_len record) ++
      encode_uint 2 (template_id record) ++
      encode_uint 4 (msg_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (body_len_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  Some ({| body_len := body_len_value; template_id := template_id_value; msg_seq_num := msg_seq_num_value |}, bytes)
              end
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

  End EobiHeader.

  Module PacketHeader.

    (** Eurex Eobi Packet Header *)
    Record t := {
      eobi_header : EobiHeader.t;
      appl_seq_num : N;
      market_segment_id : N;
      partition_id : N;
      completion_indicator : N;
      appl_seq_reset_indicator : N;
      pad5 : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      EobiHeader.bounded (eobi_header record) /\
      (appl_seq_num record < 256 ^ N.of_nat 4)%N /\
      (market_segment_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 1)%N /\
      (completion_indicator record < 256 ^ N.of_nat 1)%N /\
      (appl_seq_reset_indicator record < 256 ^ N.of_nat 1)%N /\
      (pad5 record < 256 ^ N.of_nat 5)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      EobiHeader.encode (eobi_header record) ++
      encode_uint 4 (appl_seq_num record) ++
      encode_uint 4 (market_segment_id record) ++
      encode_uint 1 (partition_id record) ++
      encode_uint 1 (completion_indicator record) ++
      encode_uint 1 (appl_seq_reset_indicator record) ++
      encode_uint 5 (pad5 record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match EobiHeader.decode bytes with
      | None => None
      | Some (eobi_header_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (market_segment_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (completion_indicator_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (appl_seq_reset_indicator_value, bytes) =>
                              match decode_uint 5 bytes with
                              | None => None
                              | Some (pad5_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (transact_time_value, bytes) =>
                                      Some ({| eobi_header := eobi_header_value; appl_seq_num := appl_seq_num_value; market_segment_id := market_segment_id_value; partition_id := partition_id_value; completion_indicator := completion_indicator_value; appl_seq_reset_indicator := appl_seq_reset_indicator_value; pad5 := pad5_value; transact_time := transact_time_value |}, bytes)
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
      rewrite !length_app, !EobiHeader.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite EobiHeader.decode_encode by exact bound_0.
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
    Proof. decide equality; solve [apply N.eq_dec | apply EobiHeader.eq_dec]. Defined.

  End PacketHeader.

  Module MessageHeaderComp.

    Record t := {
      body_len : N;
      template_id : N;
      msg_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (body_len record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 2)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (body_len record) ++
      encode_uint 2 (template_id record) ++
      encode_uint 4 (msg_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (body_len_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  Some ({| body_len := body_len_value; template_id := template_id_value; msg_seq_num := msg_seq_num_value |}, bytes)
              end
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

  End MessageHeaderComp.

  Module AuctionBbo.

    Record t := {
      transact_time : N;
      security_id : N;
      bid_px : N;
      offer_px : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (bid_px record < 256 ^ N.of_nat 8)%N /\
      (offer_px record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (security_id record) ++
      encode_uint 8 (bid_px record) ++
      encode_uint 8 (offer_px record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (bid_px_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (offer_px_value, bytes) =>
                      Some ({| transact_time := transact_time_value; security_id := security_id_value; bid_px := bid_px_value; offer_px := offer_px_value |}, bytes)
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

  End AuctionBbo.

  Module AuctionClearingPrice.

    Record t := {
      transact_time : N;
      security_id : N;
      last_px : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (security_id record) ++
      encode_uint 8 (last_px record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_px_value, bytes) =>
                  Some ({| transact_time := transact_time_value; security_id := security_id_value; last_px := last_px_value |}, bytes)
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

  End AuctionClearingPrice.

  Module CrossRequest.

    Record t := {
      security_id : N;
      last_qty : N;
      pad4 : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (security_id record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 4 (pad4 record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (last_qty_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (pad4_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (transact_time_value, bytes) =>
                      Some ({| security_id := security_id_value; last_qty := last_qty_value; pad4 := pad4_value; transact_time := transact_time_value |}, bytes)
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

  End CrossRequest.

  Module ExecutionSummary.

    Record t := {
      security_id : N;
      aggressor_timestamp : N;
      request_time : N;
      exec_id : N;
      last_qty : N;
      aggressor_side : N;
      trade_condition : N;
      pad2 : N;
      last_px : N;
      resting_hidden_qty : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (aggressor_timestamp record < 256 ^ N.of_nat 8)%N /\
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (aggressor_side record < 256 ^ N.of_nat 1)%N /\
      (trade_condition record < 256 ^ N.of_nat 1)%N /\
      (pad2 record < 256 ^ N.of_nat 2)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (resting_hidden_qty record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (security_id record) ++
      encode_uint 8 (aggressor_timestamp record) ++
      encode_uint 8 (request_time record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 1 (aggressor_side record) ++
      encode_uint 1 (trade_condition record) ++
      encode_uint 2 (pad2 record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (resting_hidden_qty record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (aggressor_timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (request_time_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (last_qty_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (aggressor_side_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (trade_condition_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (pad2_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_px_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (resting_hidden_qty_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (pad4_value, bytes) =>
                                                  Some ({| security_id := security_id_value; aggressor_timestamp := aggressor_timestamp_value; request_time := request_time_value; exec_id := exec_id_value; last_qty := last_qty_value; aggressor_side := aggressor_side_value; trade_condition := trade_condition_value; pad2 := pad2_value; last_px := last_px_value; resting_hidden_qty := resting_hidden_qty_value; pad4 := pad4_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ExecutionSummary.

  Module FullOrderExecution.

    Record t := {
      side : N;
      pad7 : N;
      price : N;
      trd_reg_ts_time_priority : N;
      security_id : N;
      trd_match_id : N;
      last_qty : N;
      last_px : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (side record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_priority record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (trd_match_id record < 256 ^ N.of_nat 4)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (side record) ++
      encode_uint 7 (pad7 record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (trd_reg_ts_time_priority record) ++
      encode_uint 8 (security_id record) ++
      encode_uint 4 (trd_match_id record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 8 (last_px record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (side_value, bytes) =>
          match decode_uint 7 bytes with
          | None => None
          | Some (pad7_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trd_reg_ts_time_priority_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (security_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trd_match_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (last_qty_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      Some ({| side := side_value; pad7 := pad7_value; price := price_value; trd_reg_ts_time_priority := trd_reg_ts_time_priority_value; security_id := security_id_value; trd_match_id := trd_match_id_value; last_qty := last_qty_value; last_px := last_px_value |}, bytes)
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

  End FullOrderExecution.

  Module Heartbeat.

    Record t := {
      last_msg_seq_num_processed : N;
      pad4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_msg_seq_num_processed record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_msg_seq_num_processed record) ++
      encode_uint 4 (pad4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_msg_seq_num_processed_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (pad4_value, bytes) =>
              Some ({| last_msg_seq_num_processed := last_msg_seq_num_processed_value; pad4 := pad4_value |}, bytes)
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

  End Heartbeat.

  Module InstrumentStateChange.

    Record t := {
      security_id : N;
      security_status : N;
      security_trading_status : N;
      fast_market_indicator : N;
      pad5 : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (security_status record < 256 ^ N.of_nat 1)%N /\
      (security_trading_status record < 256 ^ N.of_nat 1)%N /\
      (fast_market_indicator record < 256 ^ N.of_nat 1)%N /\
      (pad5 record < 256 ^ N.of_nat 5)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (security_id record) ++
      encode_uint 1 (security_status record) ++
      encode_uint 1 (security_trading_status record) ++
      encode_uint 1 (fast_market_indicator record) ++
      encode_uint 5 (pad5 record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (security_status_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (security_trading_status_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (fast_market_indicator_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (pad5_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (transact_time_value, bytes) =>
                              Some ({| security_id := security_id_value; security_status := security_status_value; security_trading_status := security_trading_status_value; fast_market_indicator := fast_market_indicator_value; pad5 := pad5_value; transact_time := transact_time_value |}, bytes)
                          end
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

  End InstrumentStateChange.

  Module OrderDetailsComp.

    Record t := {
      trd_reg_ts_time_priority : N;
      display_qty : N;
      side : N;
      pad3 : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_priority record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_priority record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 1 (side record) ++
      encode_uint 3 (pad3 record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_priority_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (display_qty_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 3 bytes with
                  | None => None
                  | Some (pad3_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          Some ({| trd_reg_ts_time_priority := trd_reg_ts_time_priority_value; display_qty := display_qty_value; side := side_value; pad3 := pad3_value; price := price_value |}, bytes)
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

  End OrderDetailsComp.

  Module OrderAdd.

    Record t := {
      trd_reg_ts_time_in : N;
      security_id : N;
      order_details_comp : OrderDetailsComp.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      OrderDetailsComp.bounded (order_details_comp record).

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (security_id record) ++
      OrderDetailsComp.encode (order_details_comp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_in_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match OrderDetailsComp.decode bytes with
              | None => None
              | Some (order_details_comp_value, bytes) =>
                  Some ({| trd_reg_ts_time_in := trd_reg_ts_time_in_value; security_id := security_id_value; order_details_comp := order_details_comp_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !OrderDetailsComp.encode_length. reflexivity.
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
      rewrite OrderDetailsComp.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply OrderDetailsComp.eq_dec]. Defined.

  End OrderAdd.

  Module OrderDetailsComp2.

    Record t := {
      trd_reg_ts_time_priority : N;
      display_qty : N;
      side : N;
      pad3 : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_priority record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_priority record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 1 (side record) ++
      encode_uint 3 (pad3 record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_priority_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (display_qty_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 3 bytes with
                  | None => None
                  | Some (pad3_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          Some ({| trd_reg_ts_time_priority := trd_reg_ts_time_priority_value; display_qty := display_qty_value; side := side_value; pad3 := pad3_value; price := price_value |}, bytes)
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

  End OrderDetailsComp2.

  Module OrderDelete.

    Record t := {
      trd_reg_ts_time_in : N;
      transact_time : N;
      security_id : N;
      order_details_comp : OrderDetailsComp2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      OrderDetailsComp2.bounded (order_details_comp record).

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (security_id record) ++
      OrderDetailsComp2.encode (order_details_comp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_in_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transact_time_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match OrderDetailsComp2.decode bytes with
                  | None => None
                  | Some (order_details_comp_value, bytes) =>
                      Some ({| trd_reg_ts_time_in := trd_reg_ts_time_in_value; transact_time := transact_time_value; security_id := security_id_value; order_details_comp := order_details_comp_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !OrderDetailsComp2.encode_length. reflexivity.
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
      rewrite OrderDetailsComp2.decode_encode by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply OrderDetailsComp2.eq_dec]. Defined.

  End OrderDelete.

  Module OrderMassDelete.

    Record t := {
      security_id : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (security_id record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transact_time_value, bytes) =>
              Some ({| security_id := security_id_value; transact_time := transact_time_value |}, bytes)
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

  End OrderMassDelete.

  Module OrderDetailsComp3.

    Record t := {
      trd_reg_ts_time_priority : N;
      display_qty : N;
      side : N;
      pad3 : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_priority record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_priority record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 1 (side record) ++
      encode_uint 3 (pad3 record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_priority_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (display_qty_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 3 bytes with
                  | None => None
                  | Some (pad3_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          Some ({| trd_reg_ts_time_priority := trd_reg_ts_time_priority_value; display_qty := display_qty_value; side := side_value; pad3 := pad3_value; price := price_value |}, bytes)
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

  End OrderDetailsComp3.

  Module OrderModify.

    Record t := {
      trd_reg_ts_time_in : N;
      trd_reg_ts_prev_time_priority : N;
      prev_price : N;
      prev_display_qty : N;
      pad4 : N;
      security_id : N;
      order_details_comp : OrderDetailsComp3.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_prev_time_priority record < 256 ^ N.of_nat 8)%N /\
      (prev_price record < 256 ^ N.of_nat 8)%N /\
      (prev_display_qty record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      OrderDetailsComp3.bounded (order_details_comp record).

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (trd_reg_ts_prev_time_priority record) ++
      encode_uint 8 (prev_price record) ++
      encode_uint 4 (prev_display_qty record) ++
      encode_uint 4 (pad4 record) ++
      encode_uint 8 (security_id record) ++
      OrderDetailsComp3.encode (order_details_comp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_in_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trd_reg_ts_prev_time_priority_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (prev_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (prev_display_qty_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (pad4_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match OrderDetailsComp3.decode bytes with
                              | None => None
                              | Some (order_details_comp_value, bytes) =>
                                  Some ({| trd_reg_ts_time_in := trd_reg_ts_time_in_value; trd_reg_ts_prev_time_priority := trd_reg_ts_prev_time_priority_value; prev_price := prev_price_value; prev_display_qty := prev_display_qty_value; pad4 := pad4_value; security_id := security_id_value; order_details_comp := order_details_comp_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !OrderDetailsComp3.encode_length. reflexivity.
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
      rewrite OrderDetailsComp3.decode_encode by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply OrderDetailsComp3.eq_dec]. Defined.

  End OrderModify.

  Module OrderDetailsComp4.

    Record t := {
      trd_reg_ts_time_priority : N;
      display_qty : N;
      side : N;
      pad3 : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_priority record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_priority record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 1 (side record) ++
      encode_uint 3 (pad3 record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_priority_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (display_qty_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 3 bytes with
                  | None => None
                  | Some (pad3_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          Some ({| trd_reg_ts_time_priority := trd_reg_ts_time_priority_value; display_qty := display_qty_value; side := side_value; pad3 := pad3_value; price := price_value |}, bytes)
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

  End OrderDetailsComp4.

  Module OrderModifySamePrio.

    Record t := {
      trd_reg_ts_time_in : N;
      transact_time : N;
      prev_display_qty : N;
      pad4 : N;
      security_id : N;
      order_details_comp : OrderDetailsComp4.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_in record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (prev_display_qty record < 256 ^ N.of_nat 4)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      OrderDetailsComp4.bounded (order_details_comp record).

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_in record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (prev_display_qty record) ++
      encode_uint 4 (pad4 record) ++
      encode_uint 8 (security_id record) ++
      OrderDetailsComp4.encode (order_details_comp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_in_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transact_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (prev_display_qty_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (pad4_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (security_id_value, bytes) =>
                          match OrderDetailsComp4.decode bytes with
                          | None => None
                          | Some (order_details_comp_value, bytes) =>
                              Some ({| trd_reg_ts_time_in := trd_reg_ts_time_in_value; transact_time := transact_time_value; prev_display_qty := prev_display_qty_value; pad4 := pad4_value; security_id := security_id_value; order_details_comp := order_details_comp_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !OrderDetailsComp4.encode_length. reflexivity.
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
      rewrite OrderDetailsComp4.decode_encode by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply OrderDetailsComp4.eq_dec]. Defined.

  End OrderModifySamePrio.

  Module PartialOrderExecution.

    Record t := {
      side : N;
      pad7 : N;
      price : N;
      trd_reg_ts_time_priority : N;
      security_id : N;
      trd_match_id : N;
      last_qty : N;
      last_px : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (side record < 256 ^ N.of_nat 1)%N /\
      (pad7 record < 256 ^ N.of_nat 7)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (trd_reg_ts_time_priority record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (trd_match_id record < 256 ^ N.of_nat 4)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (side record) ++
      encode_uint 7 (pad7 record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (trd_reg_ts_time_priority record) ++
      encode_uint 8 (security_id record) ++
      encode_uint 4 (trd_match_id record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 8 (last_px record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (side_value, bytes) =>
          match decode_uint 7 bytes with
          | None => None
          | Some (pad7_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trd_reg_ts_time_priority_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (security_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trd_match_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (last_qty_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      Some ({| side := side_value; pad7 := pad7_value; price := price_value; trd_reg_ts_time_priority := trd_reg_ts_time_priority_value; security_id := security_id_value; trd_match_id := trd_match_id_value; last_qty := last_qty_value; last_px := last_px_value |}, bytes)
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

  End PartialOrderExecution.

  Module ProductStateChange.

    Record t := {
      trading_session_id : N;
      trading_session_sub_id : N;
      trad_ses_status : N;
      fast_market_indicator : N;
      pad4 : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (trading_session_sub_id record < 256 ^ N.of_nat 1)%N /\
      (trad_ses_status record < 256 ^ N.of_nat 1)%N /\
      (fast_market_indicator record < 256 ^ N.of_nat 1)%N /\
      (pad4 record < 256 ^ N.of_nat 4)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (trading_session_id record) ++
      encode_uint 1 (trading_session_sub_id record) ++
      encode_uint 1 (trad_ses_status record) ++
      encode_uint 1 (fast_market_indicator record) ++
      encode_uint 4 (pad4 record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (trading_session_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (trading_session_sub_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trad_ses_status_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (fast_market_indicator_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (pad4_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (transact_time_value, bytes) =>
                              Some ({| trading_session_id := trading_session_id_value; trading_session_sub_id := trading_session_sub_id_value; trad_ses_status := trad_ses_status_value; fast_market_indicator := fast_market_indicator_value; pad4 := pad4_value; transact_time := transact_time_value |}, bytes)
                          end
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

  End ProductStateChange.

  Module ProductSummary.

    Record t := {
      last_msg_seq_num_processed : N;
      trading_session_id : N;
      trading_session_sub_id : N;
      trad_ses_status : N;
      fast_market_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_msg_seq_num_processed record < 256 ^ N.of_nat 4)%N /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (trading_session_sub_id record < 256 ^ N.of_nat 1)%N /\
      (trad_ses_status record < 256 ^ N.of_nat 1)%N /\
      (fast_market_indicator record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_msg_seq_num_processed record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 1 (trading_session_sub_id record) ++
      encode_uint 1 (trad_ses_status record) ++
      encode_uint 1 (fast_market_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_msg_seq_num_processed_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (trading_session_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_session_sub_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (trad_ses_status_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (fast_market_indicator_value, bytes) =>
                          Some ({| last_msg_seq_num_processed := last_msg_seq_num_processed_value; trading_session_id := trading_session_id_value; trading_session_sub_id := trading_session_sub_id_value; trad_ses_status := trad_ses_status_value; fast_market_indicator := fast_market_indicator_value |}, bytes)
                      end
                  end
              end
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

  End ProductSummary.

  Module QuoteRequest.

    Record t := {
      security_id : N;
      last_qty : N;
      side : N;
      pad3 : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (security_id record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 1 (side record) ++
      encode_uint 3 (pad3 record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (last_qty_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 3 bytes with
                  | None => None
                  | Some (pad3_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (transact_time_value, bytes) =>
                          Some ({| security_id := security_id_value; last_qty := last_qty_value; side := side_value; pad3 := pad3_value; transact_time := transact_time_value |}, bytes)
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

  End QuoteRequest.

  Module OrderDetailsComp5.

    Record t := {
      trd_reg_ts_time_priority : N;
      display_qty : N;
      side : N;
      pad3 : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trd_reg_ts_time_priority record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (pad3 record < 256 ^ N.of_nat 3)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trd_reg_ts_time_priority record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 1 (side record) ++
      encode_uint 3 (pad3 record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trd_reg_ts_time_priority_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (display_qty_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 3 bytes with
                  | None => None
                  | Some (pad3_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          Some ({| trd_reg_ts_time_priority := trd_reg_ts_time_priority_value; display_qty := display_qty_value; side := side_value; pad3 := pad3_value; price := price_value |}, bytes)
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

  End OrderDetailsComp5.

  Module SnapshotOrder.

    Record t := {
      order_details_comp : OrderDetailsComp5.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OrderDetailsComp5.bounded (order_details_comp record).

    Definition encode (record : t) : list byte :=
      OrderDetailsComp5.encode (order_details_comp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OrderDetailsComp5.decode bytes with
      | None => None
      | Some (order_details_comp_value, bytes) =>
          Some ({| order_details_comp := order_details_comp_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !OrderDetailsComp5.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite OrderDetailsComp5.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply OrderDetailsComp5.eq_dec]. Defined.

  End SnapshotOrder.

  Module TopOfBook.

    Record t := {
      transact_time : N;
      security_id : N;
      bid_px : N;
      offer_px : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (bid_px record < 256 ^ N.of_nat 8)%N /\
      (offer_px record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (security_id record) ++
      encode_uint 8 (bid_px record) ++
      encode_uint 8 (offer_px record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (bid_px_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (offer_px_value, bytes) =>
                      Some ({| transact_time := transact_time_value; security_id := security_id_value; bid_px := bid_px_value; offer_px := offer_px_value |}, bytes)
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

  End TopOfBook.

  Module TradeReport.

    Record t := {
      security_id : N;
      transact_time : N;
      trd_match_id : N;
      last_qty : N;
      last_px : N;
      match_type : N;
      match_sub_type : N;
      pad6 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (trd_match_id record < 256 ^ N.of_nat 4)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (match_type record < 256 ^ N.of_nat 1)%N /\
      (match_sub_type record < 256 ^ N.of_nat 1)%N /\
      (pad6 record < 256 ^ N.of_nat 6)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (security_id record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (trd_match_id record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 1 (match_type record) ++
      encode_uint 1 (match_sub_type record) ++
      encode_uint 6 (pad6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transact_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trd_match_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (last_qty_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_px_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (match_type_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (match_sub_type_value, bytes) =>
                                  match decode_uint 6 bytes with
                                  | None => None
                                  | Some (pad6_value, bytes) =>
                                      Some ({| security_id := security_id_value; transact_time := transact_time_value; trd_match_id := trd_match_id_value; last_qty := last_qty_value; last_px := last_px_value; match_type := match_type_value; match_sub_type := match_sub_type_value; pad6 := pad6_value |}, bytes)
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

  End TradeReport.

End EurexT7EobiV25.
