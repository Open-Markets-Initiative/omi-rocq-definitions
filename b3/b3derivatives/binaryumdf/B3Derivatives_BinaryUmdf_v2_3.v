From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Brasil, Bolsa, Balcão Binary Unified Market Data Feed

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
      - a block whose stated length holds more than its fields
      - a run counted by a field
      - a field present only on a condition

    License: MIT No Attribution
  *)

Module B3DerivativesBinaryUmdfV23.

  Module PacketHeader.

    (** B3 Mdp Packet Header *)
    Record t := {
      channel_id : N;
      packet_reserved : N;
      sequence_version : N;
      sequence_number : N;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_id record < 256 ^ N.of_nat 1)%N /\
      (packet_reserved record < 256 ^ N.of_nat 1)%N /\
      (sequence_version record < 256 ^ N.of_nat 2)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (channel_id record) ++
      encode_uint 1 (packet_reserved record) ++
      encode_uint 2 (sequence_version record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (channel_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (packet_reserved_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (sequence_version_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          Some ({| channel_id := channel_id_value; packet_reserved := packet_reserved_value; sequence_version := sequence_version_value; sequence_number := sequence_number_value; sending_time := sending_time_value |}, bytes)
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

  End PacketHeader.

  Module FramingHeader.

    (** B3 Sbe framing header *)
    Record t := {
      message_length : N;
      encoding_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (encoding_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 2 (encoding_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (encoding_type_value, bytes) =>
              Some ({| message_length := message_length_value; encoding_type := encoding_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End FramingHeader.

  Module MessageHeader.

    (** B3 Sbe message header — message identifiers and length of message root *)
    Record t := {
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 2)%N /\
      (schema_id record < 256 ^ N.of_nat 2)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 2 (template_id record) ++
      encode_uint 2 (schema_id record) ++
      encode_uint 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint 2 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End MessageHeader.

  Module SequenceMessage.

    (** Sequence_2Message *)
    Record t := {
      next_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (next_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (next_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (next_seq_no_value, bytes) =>
          Some ({| next_seq_no := next_seq_no_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SequenceMessage.

  Module MaturityMonthYear.

    (** SecurityDefinition_12Message *)
    Record t := {
      year : N;
      month : N;
      day : N;
      week : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (year record < 256 ^ N.of_nat 2)%N /\
      (month record < 256 ^ N.of_nat 1)%N /\
      (day record < 256 ^ N.of_nat 1)%N /\
      (week record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (year record) ++
      encode_uint 1 (month record) ++
      encode_uint 1 (day record) ++
      encode_uint 1 (week record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (week_value, bytes) =>
                      Some ({| year := year_value; month := month_value; day := day_value; week := week_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End MaturityMonthYear.

  Module ContractSettlMonth.

    (** SecurityDefinition_12Message *)
    Record t := {
      year : N;
      month : N;
      day : N;
      week : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (year record < 256 ^ N.of_nat 2)%N /\
      (month record < 256 ^ N.of_nat 1)%N /\
      (day record < 256 ^ N.of_nat 1)%N /\
      (week record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (year record) ++
      encode_uint 1 (month record) ++
      encode_uint 1 (day record) ++
      encode_uint 1 (week record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (week_value, bytes) =>
                      Some ({| year := year_value; month := month_value; day := day_value; week := week_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End ContractSettlMonth.

  Module GroupSizeEncoding.

    (** GroupSizeEncoding *)
    Record t := {
      block_length : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length := block_length_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding.

  Module SnapshotFullRefreshHeader30Message.

    (** SnapshotFullRefresh_Header_30Message *)
    Record t := {
      security_id : N;
      last_msg_seq_num_processed : N;
      tot_num_reports : N;
      tot_num_bids : N;
      tot_num_offers : N;
      tot_num_stats : N;
      offset_26_padding_2 : list byte;
      last_rpt_seq : N;
      last_sequence_version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (last_msg_seq_num_processed record < 256 ^ N.of_nat 4)%N /\
      (tot_num_reports record < 256 ^ N.of_nat 4)%N /\
      (tot_num_bids record < 256 ^ N.of_nat 4)%N /\
      (tot_num_offers record < 256 ^ N.of_nat 4)%N /\
      (tot_num_stats record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (offset_26_padding_2 record) = 2 /\
      (last_rpt_seq record < 256 ^ N.of_nat 4)%N /\
      (last_sequence_version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (security_id record) ++
      encode_uint 4 (last_msg_seq_num_processed record) ++
      encode_uint 4 (tot_num_reports record) ++
      encode_uint 4 (tot_num_bids record) ++
      encode_uint 4 (tot_num_offers record) ++
      encode_uint 2 (tot_num_stats record) ++
      encode_bytes 2 (offset_26_padding_2 record) ++
      encode_uint 4 (last_rpt_seq record) ++
      encode_uint 2 (last_sequence_version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (last_msg_seq_num_processed_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tot_num_reports_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (tot_num_bids_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (tot_num_offers_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (tot_num_stats_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (offset_26_padding_2_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (last_rpt_seq_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (last_sequence_version_value, bytes) =>
                                          Some ({| security_id := security_id_value; last_msg_seq_num_processed := last_msg_seq_num_processed_value; tot_num_reports := tot_num_reports_value; tot_num_bids := tot_num_bids_value; tot_num_offers := tot_num_offers_value; tot_num_stats := tot_num_stats_value; offset_26_padding_2 := offset_26_padding_2_value; last_rpt_seq := last_rpt_seq_value; last_sequence_version := last_sequence_version_value |}, bytes)
                                      end
                                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SnapshotFullRefreshHeader30Message.

  Module ExecutionSummary55Message.

    (** ExecutionSummary_55Message *)
    Record t := {
      security_id : N;
      offset_8_padding_2 : list byte;
      aggressor_side : N;
      offset_11_padding_1 : list byte;
      last_px : N;
      fill_qty : N;
      traded_hidden_qty : N;
      cxl_qty : N;
      aggressor_time : N;
      rpt_seq : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (offset_8_padding_2 record) = 2 /\
      (aggressor_side record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (offset_11_padding_1 record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (fill_qty record < 256 ^ N.of_nat 8)%N /\
      (traded_hidden_qty record < 256 ^ N.of_nat 8)%N /\
      (cxl_qty record < 256 ^ N.of_nat 8)%N /\
      (aggressor_time record < 256 ^ N.of_nat 8)%N /\
      (rpt_seq record < 256 ^ N.of_nat 4)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (security_id record) ++
      encode_bytes 2 (offset_8_padding_2 record) ++
      encode_uint 1 (aggressor_side record) ++
      encode_bytes 1 (offset_11_padding_1 record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (fill_qty record) ++
      encode_uint 8 (traded_hidden_qty record) ++
      encode_uint 8 (cxl_qty record) ++
      encode_uint 8 (aggressor_time record) ++
      encode_uint 4 (rpt_seq record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (offset_8_padding_2_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (aggressor_side_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (offset_11_padding_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_px_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (fill_qty_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (traded_hidden_qty_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (cxl_qty_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (aggressor_time_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (rpt_seq_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (transact_time_value, bytes) =>
                                                  Some ({| security_id := security_id_value; offset_8_padding_2 := offset_8_padding_2_value; aggressor_side := aggressor_side_value; offset_11_padding_1 := offset_11_padding_1_value; last_px := last_px_value; fill_qty := fill_qty_value; traded_hidden_qty := traded_hidden_qty_value; cxl_qty := cxl_qty_value; aggressor_time := aggressor_time_value; rpt_seq := rpt_seq_value; transact_time := transact_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
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

  End ExecutionSummary55Message.

End B3DerivativesBinaryUmdfV23.
