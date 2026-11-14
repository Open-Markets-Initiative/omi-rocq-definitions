From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Euronext Order Entry Gateway

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

    License: MIT No Attribution
  *)

Module EuronextOptiqOrderEntryGatewayV13.

  Module FrameHeader.

    (** Optiq length prefix, read before the message it frames *)
    Record t := {
      frame : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (frame record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (frame record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (frame_value, bytes) =>
          Some ({| frame := frame_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint_le by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End FrameHeader.

  Module MessageHeader.

    (** Optiq Sbe message header — message identifiers and length of message root *)
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
      encode_uint_le 2 (block_length record) ++
      encode_uint_le 2 (template_id record) ++
      encode_uint_le 2 (schema_id record) ++
      encode_uint_le 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint_le 2 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint_le 2 bytes with
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
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MessageHeader.

  Module GroupSizeEncoding.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  Module KillMessage.

    (** KillMessage *)
    Record t := {
      msg_seq_num : N;
      firm_id : list byte;
      sending_time_optional : N;
      oeg_in_from_member : N;
      oeg_out_time_to_me : N;
      book_in : N;
      book_out_time_optional : N;
      oeg_in_from_me_optional : N;
      oeg_out_to_member_optional : N;
      client_order_id_optional : N;
      orig_client_order_id : N;
      order_id : N;
      symbol_index : N;
      emm : N;
      kill_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time_optional record < 256 ^ N.of_nat 8)%N /\
      (oeg_in_from_member record < 256 ^ N.of_nat 8)%N /\
      (oeg_out_time_to_me record < 256 ^ N.of_nat 8)%N /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (book_out_time_optional record < 256 ^ N.of_nat 8)%N /\
      (oeg_in_from_me_optional record < 256 ^ N.of_nat 8)%N /\
      (oeg_out_to_member_optional record < 256 ^ N.of_nat 8)%N /\
      (client_order_id_optional record < 256 ^ N.of_nat 8)%N /\
      (orig_client_order_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (kill_reason record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time_optional record) ++
      encode_uint_le 8 (oeg_in_from_member record) ++
      encode_uint_le 8 (oeg_out_time_to_me record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (book_out_time_optional record) ++
      encode_uint_le 8 (oeg_in_from_me_optional record) ++
      encode_uint_le 8 (oeg_out_to_member_optional record) ++
      encode_uint_le 8 (client_order_id_optional record) ++
      encode_uint_le 8 (orig_client_order_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 2 (kill_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_optional_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (oeg_in_from_member_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (oeg_out_time_to_me_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (book_in_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (book_out_time_optional_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (oeg_in_from_me_optional_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (oeg_out_to_member_optional_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (client_order_id_optional_value, bytes) =>
                                              match decode_uint_le 8 bytes with
                                              | None => None
                                              | Some (orig_client_order_id_value, bytes) =>
                                                  match decode_uint_le 8 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_uint_le 4 bytes with
                                                      | None => None
                                                      | Some (symbol_index_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (emm_value, bytes) =>
                                                              match decode_uint_le 2 bytes with
                                                              | None => None
                                                              | Some (kill_reason_value, bytes) =>
                                                                  Some ({| msg_seq_num := msg_seq_num_value; firm_id := firm_id_value; sending_time_optional := sending_time_optional_value; oeg_in_from_member := oeg_in_from_member_value; oeg_out_time_to_me := oeg_out_time_to_me_value; book_in := book_in_value; book_out_time_optional := book_out_time_optional_value; oeg_in_from_me_optional := oeg_in_from_me_optional_value; oeg_out_to_member_optional := oeg_out_to_member_optional_value; client_order_id_optional := client_order_id_optional_value; orig_client_order_id := orig_client_order_id_value; order_id := order_id_value; symbol_index := symbol_index_value; emm := emm_value; kill_reason := kill_reason_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 99.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint_le by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End KillMessage.

  Module QuoteRequestMessage.

    (** QuoteRequestMessage *)
    Record t := {
      cl_msg_seq_num : N;
      firm_id : list byte;
      sending_time : N;
      execution_within_firm_short_code : N;
      client_identification_shortcode : N;
      client_order_id : N;
      order_qty : N;
      symbol_index : N;
      emm : N;
      side_optional : N;
      firm_id_publication : N;
      end_client : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (execution_within_firm_short_code record < 256 ^ N.of_nat 4)%N /\
      (client_identification_shortcode record < 256 ^ N.of_nat 4)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (side_optional record < 256 ^ N.of_nat 1)%N /\
      (firm_id_publication record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (end_client record) = 11.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (cl_msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time record) ++
      encode_uint_le 4 (execution_within_firm_short_code record) ++
      encode_uint_le 4 (client_identification_shortcode record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (order_qty record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint 1 (side_optional record) ++
      encode_uint 1 (firm_id_publication record) ++
      encode_bytes 11 (end_client record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (cl_msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (execution_within_firm_short_code_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_identification_shortcode_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (order_qty_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (symbol_index_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (emm_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (side_optional_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (firm_id_publication_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (end_client_value, bytes) =>
                                                      Some ({| cl_msg_seq_num := cl_msg_seq_num_value; firm_id := firm_id_value; sending_time := sending_time_value; execution_within_firm_short_code := execution_within_firm_short_code_value; client_identification_shortcode := client_identification_shortcode_value; client_order_id := client_order_id_value; order_qty := order_qty_value; symbol_index := symbol_index_value; emm := emm_value; side_optional := side_optional_value; firm_id_publication := firm_id_publication_value; end_client := end_client_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteRequestMessage.

  Module CancelRequestMessage.

    (** CancelRequestMessage *)
    Record t := {
      cl_msg_seq_num : N;
      firm_id : list byte;
      sending_time : N;
      execution_within_firm_short_code : N;
      client_identification_shortcode : N;
      client_order_id : N;
      order_id_optional : N;
      orig_client_order_id : N;
      symbol_index : N;
      emm : N;
      side : N;
      order_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (execution_within_firm_short_code record < 256 ^ N.of_nat 4)%N /\
      (client_identification_shortcode record < 256 ^ N.of_nat 4)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (order_id_optional record < 256 ^ N.of_nat 8)%N /\
      (orig_client_order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (order_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (cl_msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time record) ++
      encode_uint_le 4 (execution_within_firm_short_code record) ++
      encode_uint_le 4 (client_identification_shortcode record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (order_id_optional record) ++
      encode_uint_le 8 (orig_client_order_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint 1 (side record) ++
      encode_uint 1 (order_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (cl_msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (execution_within_firm_short_code_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_identification_shortcode_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (order_id_optional_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (orig_client_order_id_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (symbol_index_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (emm_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (order_type_value, bytes) =>
                                                      Some ({| cl_msg_seq_num := cl_msg_seq_num_value; firm_id := firm_id_value; sending_time := sending_time_value; execution_within_firm_short_code := execution_within_firm_short_code_value; client_identification_shortcode := client_identification_shortcode_value; client_order_id := client_order_id_value; order_id_optional := order_id_optional_value; orig_client_order_id := orig_client_order_id_value; symbol_index := symbol_index_value; emm := emm_value; side := side_value; order_type := order_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelRequestMessage.

  Module MassCancelMessage.

    (** MassCancelMessage *)
    Record t := {
      cl_msg_seq_num : N;
      firm_id : list byte;
      sending_time : N;
      execution_within_firm_short_code : N;
      client_identification_shortcode : N;
      client_order_id : N;
      symbol_index_optional : N;
      emm_optional : N;
      instrument_group_code : list byte;
      side_optional : N;
      logical_access_id_optional : N;
      oe_partition_id_optional : N;
      contract_id : N;
      maturity : list byte;
      account_type_optional : N;
      option_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (execution_within_firm_short_code record < 256 ^ N.of_nat 4)%N /\
      (client_identification_shortcode record < 256 ^ N.of_nat 4)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index_optional record < 256 ^ N.of_nat 4)%N /\
      (emm_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (instrument_group_code record) = 2 /\
      (side_optional record < 256 ^ N.of_nat 1)%N /\
      (logical_access_id_optional record < 256 ^ N.of_nat 4)%N /\
      (oe_partition_id_optional record < 256 ^ N.of_nat 2)%N /\
      (contract_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (maturity record) = 8 /\
      (account_type_optional record < 256 ^ N.of_nat 1)%N /\
      (option_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (cl_msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time record) ++
      encode_uint_le 4 (execution_within_firm_short_code record) ++
      encode_uint_le 4 (client_identification_shortcode record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 4 (symbol_index_optional record) ++
      encode_uint 1 (emm_optional record) ++
      encode_bytes 2 (instrument_group_code record) ++
      encode_uint 1 (side_optional record) ++
      encode_uint_le 4 (logical_access_id_optional record) ++
      encode_uint_le 2 (oe_partition_id_optional record) ++
      encode_uint_le 4 (contract_id record) ++
      encode_bytes 8 (maturity record) ++
      encode_uint 1 (account_type_optional record) ++
      encode_uint 1 (option_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (cl_msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (execution_within_firm_short_code_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_identification_shortcode_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (symbol_index_optional_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (emm_optional_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (instrument_group_code_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (side_optional_value, bytes) =>
                                              match decode_uint_le 4 bytes with
                                              | None => None
                                              | Some (logical_access_id_optional_value, bytes) =>
                                                  match decode_uint_le 2 bytes with
                                                  | None => None
                                                  | Some (oe_partition_id_optional_value, bytes) =>
                                                      match decode_uint_le 4 bytes with
                                                      | None => None
                                                      | Some (contract_id_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (maturity_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (account_type_optional_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (option_type_value, bytes) =>
                                                                      Some ({| cl_msg_seq_num := cl_msg_seq_num_value; firm_id := firm_id_value; sending_time := sending_time_value; execution_within_firm_short_code := execution_within_firm_short_code_value; client_identification_shortcode := client_identification_shortcode_value; client_order_id := client_order_id_value; symbol_index_optional := symbol_index_optional_value; emm_optional := emm_optional_value; instrument_group_code := instrument_group_code_value; side_optional := side_optional_value; logical_access_id_optional := logical_access_id_optional_value; oe_partition_id_optional := oe_partition_id_optional_value; contract_id := contract_id_value; maturity := maturity_value; account_type_optional := account_type_optional_value; option_type := option_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelMessage.

  Module MassCancelAckMessage.

    (** MassCancelAckMessage *)
    Record t := {
      msg_seq_num : N;
      firm_id : list byte;
      sending_time_optional : N;
      oeg_in_from_member : N;
      oeg_out_time_to_me : N;
      book_in : N;
      book_out_time : N;
      oeg_in_from_me : N;
      oeg_out_to_member : N;
      client_order_id : N;
      total_affected_orders : N;
      symbol_index_optional : N;
      emm_optional : N;
      instrument_group_code : list byte;
      side_optional : N;
      logical_access_id_optional : N;
      oe_partition_id_optional : N;
      contract_id : N;
      maturity : list byte;
      account_type_optional : N;
      option_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time_optional record < 256 ^ N.of_nat 8)%N /\
      (oeg_in_from_member record < 256 ^ N.of_nat 8)%N /\
      (oeg_out_time_to_me record < 256 ^ N.of_nat 8)%N /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (book_out_time record < 256 ^ N.of_nat 8)%N /\
      (oeg_in_from_me record < 256 ^ N.of_nat 8)%N /\
      (oeg_out_to_member record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (total_affected_orders record < 256 ^ N.of_nat 4)%N /\
      (symbol_index_optional record < 256 ^ N.of_nat 4)%N /\
      (emm_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (instrument_group_code record) = 2 /\
      (side_optional record < 256 ^ N.of_nat 1)%N /\
      (logical_access_id_optional record < 256 ^ N.of_nat 4)%N /\
      (oe_partition_id_optional record < 256 ^ N.of_nat 2)%N /\
      (contract_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (maturity record) = 8 /\
      (account_type_optional record < 256 ^ N.of_nat 1)%N /\
      (option_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time_optional record) ++
      encode_uint_le 8 (oeg_in_from_member record) ++
      encode_uint_le 8 (oeg_out_time_to_me record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (book_out_time record) ++
      encode_uint_le 8 (oeg_in_from_me record) ++
      encode_uint_le 8 (oeg_out_to_member record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 4 (total_affected_orders record) ++
      encode_uint_le 4 (symbol_index_optional record) ++
      encode_uint 1 (emm_optional record) ++
      encode_bytes 2 (instrument_group_code record) ++
      encode_uint 1 (side_optional record) ++
      encode_uint_le 4 (logical_access_id_optional record) ++
      encode_uint_le 2 (oe_partition_id_optional record) ++
      encode_uint_le 4 (contract_id record) ++
      encode_bytes 8 (maturity record) ++
      encode_uint 1 (account_type_optional record) ++
      encode_uint 1 (option_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_optional_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (oeg_in_from_member_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (oeg_out_time_to_me_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (book_in_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (book_out_time_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (oeg_in_from_me_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (oeg_out_to_member_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (client_order_id_value, bytes) =>
                                              match decode_uint_le 4 bytes with
                                              | None => None
                                              | Some (total_affected_orders_value, bytes) =>
                                                  match decode_uint_le 4 bytes with
                                                  | None => None
                                                  | Some (symbol_index_optional_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (emm_optional_value, bytes) =>
                                                          match decode_bytes 2 bytes with
                                                          | None => None
                                                          | Some (instrument_group_code_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (side_optional_value, bytes) =>
                                                                  match decode_uint_le 4 bytes with
                                                                  | None => None
                                                                  | Some (logical_access_id_optional_value, bytes) =>
                                                                      match decode_uint_le 2 bytes with
                                                                      | None => None
                                                                      | Some (oe_partition_id_optional_value, bytes) =>
                                                                          match decode_uint_le 4 bytes with
                                                                          | None => None
                                                                          | Some (contract_id_value, bytes) =>
                                                                              match decode_bytes 8 bytes with
                                                                              | None => None
                                                                              | Some (maturity_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (account_type_optional_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (option_type_value, bytes) =>
                                                                                          Some ({| msg_seq_num := msg_seq_num_value; firm_id := firm_id_value; sending_time_optional := sending_time_optional_value; oeg_in_from_member := oeg_in_from_member_value; oeg_out_time_to_me := oeg_out_time_to_me_value; book_in := book_in_value; book_out_time := book_out_time_value; oeg_in_from_me := oeg_in_from_me_value; oeg_out_to_member := oeg_out_to_member_value; client_order_id := client_order_id_value; total_affected_orders := total_affected_orders_value; symbol_index_optional := symbol_index_optional_value; emm_optional := emm_optional_value; instrument_group_code := instrument_group_code_value; side_optional := side_optional_value; logical_access_id_optional := logical_access_id_optional_value; oe_partition_id_optional := oe_partition_id_optional_value; contract_id := contract_id_value; maturity := maturity_value; account_type_optional := account_type_optional_value; option_type := option_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 108.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      rewrite decode_encode_uint_le by exact bound_16.
      rewrite decode_encode_uint_le by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelAckMessage.

  Module OpenOrderRequestMessage.

    (** OpenOrderRequestMessage *)
    Record t := {
      cl_msg_seq_num : N;
      firm_id : list byte;
      sending_time : N;
      execution_within_firm_short_code : N;
      client_identification_shortcode : N;
      client_order_id : N;
      order_id_optional : N;
      orig_client_order_id : N;
      symbol_index : N;
      emm : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (execution_within_firm_short_code record < 256 ^ N.of_nat 4)%N /\
      (client_identification_shortcode record < 256 ^ N.of_nat 4)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (order_id_optional record < 256 ^ N.of_nat 8)%N /\
      (orig_client_order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (cl_msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time record) ++
      encode_uint_le 4 (execution_within_firm_short_code record) ++
      encode_uint_le 4 (client_identification_shortcode record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (order_id_optional record) ++
      encode_uint_le 8 (orig_client_order_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (cl_msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (execution_within_firm_short_code_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_identification_shortcode_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (order_id_optional_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (orig_client_order_id_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (symbol_index_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (emm_value, bytes) =>
                                              Some ({| cl_msg_seq_num := cl_msg_seq_num_value; firm_id := firm_id_value; sending_time := sending_time_value; execution_within_firm_short_code := execution_within_firm_short_code_value; client_identification_shortcode := client_identification_shortcode_value; client_order_id := client_order_id_value; order_id_optional := order_id_optional_value; orig_client_order_id := orig_client_order_id_value; symbol_index := symbol_index_value; emm := emm_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpenOrderRequestMessage.

  Module OwnershipRequestAckMessage.

    (** OwnershipRequestAckMessage *)
    Record t := {
      msg_seq_num : N;
      firm_id : list byte;
      client_order_id : N;
      order_id_optional : N;
      symbol_index : N;
      logical_access_id_optional : N;
      oe_partition_id_optional : N;
      total_affected_orders : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (order_id_optional record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (logical_access_id_optional record < 256 ^ N.of_nat 4)%N /\
      (oe_partition_id_optional record < 256 ^ N.of_nat 2)%N /\
      (total_affected_orders record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (order_id_optional record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint_le 4 (logical_access_id_optional record) ++
      encode_uint_le 2 (oe_partition_id_optional record) ++
      encode_uint_le 4 (total_affected_orders record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (order_id_optional_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (symbol_index_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (logical_access_id_optional_value, bytes) =>
                              match decode_uint_le 2 bytes with
                              | None => None
                              | Some (oe_partition_id_optional_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (total_affected_orders_value, bytes) =>
                                      Some ({| msg_seq_num := msg_seq_num_value; firm_id := firm_id_value; client_order_id := client_order_id_value; order_id_optional := order_id_optional_value; symbol_index := symbol_index_value; logical_access_id_optional := logical_access_id_optional_value; oe_partition_id_optional := oe_partition_id_optional_value; total_affected_orders := total_affected_orders_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OwnershipRequestAckMessage.

  Module OwnershipRequestMessage.

    (** OwnershipRequestMessage *)
    Record t := {
      cl_msg_seq_num : N;
      firm_id : list byte;
      sending_time : N;
      execution_within_firm_short_code : N;
      client_identification_shortcode : N;
      client_order_id : N;
      order_id_optional : N;
      orig_client_order_id : N;
      symbol_index : N;
      emm : N;
      logical_access_id_optional : N;
      oe_partition_id_optional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (execution_within_firm_short_code record < 256 ^ N.of_nat 4)%N /\
      (client_identification_shortcode record < 256 ^ N.of_nat 4)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (order_id_optional record < 256 ^ N.of_nat 8)%N /\
      (orig_client_order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (logical_access_id_optional record < 256 ^ N.of_nat 4)%N /\
      (oe_partition_id_optional record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (cl_msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time record) ++
      encode_uint_le 4 (execution_within_firm_short_code record) ++
      encode_uint_le 4 (client_identification_shortcode record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (order_id_optional record) ++
      encode_uint_le 8 (orig_client_order_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 4 (logical_access_id_optional record) ++
      encode_uint_le 2 (oe_partition_id_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (cl_msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (execution_within_firm_short_code_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_identification_shortcode_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (order_id_optional_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (orig_client_order_id_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (symbol_index_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (emm_value, bytes) =>
                                              match decode_uint_le 4 bytes with
                                              | None => None
                                              | Some (logical_access_id_optional_value, bytes) =>
                                                  match decode_uint_le 2 bytes with
                                                  | None => None
                                                  | Some (oe_partition_id_optional_value, bytes) =>
                                                      Some ({| cl_msg_seq_num := cl_msg_seq_num_value; firm_id := firm_id_value; sending_time := sending_time_value; execution_within_firm_short_code := execution_within_firm_short_code_value; client_identification_shortcode := client_identification_shortcode_value; client_order_id := client_order_id_value; order_id_optional := order_id_optional_value; orig_client_order_id := orig_client_order_id_value; symbol_index := symbol_index_value; emm := emm_value; logical_access_id_optional := logical_access_id_optional_value; oe_partition_id_optional := oe_partition_id_optional_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OwnershipRequestMessage.

  Module TradeBustNotificationMessage.

    (** TradeBustNotificationMessage *)
    Record t := {
      msg_seq_num : N;
      firm_id : list byte;
      book_in : N;
      book_out_time_optional : N;
      oeg_in_from_me_optional : N;
      oeg_out_to_member_optional : N;
      symbol_index : N;
      emm : N;
      execution_id : N;
      last_traded_px : N;
      last_shares : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (book_out_time_optional record < 256 ^ N.of_nat 8)%N /\
      (oeg_in_from_me_optional record < 256 ^ N.of_nat 8)%N /\
      (oeg_out_to_member_optional record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (execution_id record < 256 ^ N.of_nat 4)%N /\
      (last_traded_px record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (book_out_time_optional record) ++
      encode_uint_le 8 (oeg_in_from_me_optional record) ++
      encode_uint_le 8 (oeg_out_to_member_optional record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 4 (execution_id record) ++
      encode_uint_le 8 (last_traded_px record) ++
      encode_uint_le 8 (last_shares record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (book_in_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (book_out_time_optional_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (oeg_in_from_me_optional_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (oeg_out_to_member_optional_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (symbol_index_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (emm_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (execution_id_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (last_traded_px_value, bytes) =>
                                              match decode_uint_le 8 bytes with
                                              | None => None
                                              | Some (last_shares_value, bytes) =>
                                                  Some ({| msg_seq_num := msg_seq_num_value; firm_id := firm_id_value; book_in := book_in_value; book_out_time_optional := book_out_time_optional_value; oeg_in_from_me_optional := oeg_in_from_me_optional_value; oeg_out_to_member_optional := oeg_out_to_member_optional_value; symbol_index := symbol_index_value; emm := emm_value; execution_id := execution_id_value; last_traded_px := last_traded_px_value; last_shares := last_shares_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 69.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeBustNotificationMessage.

  Module CollarBreachConfirmationMessage.

    (** CollarBreachConfirmationMessage *)
    Record t := {
      cl_msg_seq_num : N;
      firm_id : list byte;
      sending_time : N;
      execution_within_firm_short_code : N;
      client_identification_shortcode : N;
      client_order_id : N;
      symbol_index : N;
      emm : N;
      order_id_optional : N;
      orig_client_order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (execution_within_firm_short_code record < 256 ^ N.of_nat 4)%N /\
      (client_identification_shortcode record < 256 ^ N.of_nat 4)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (order_id_optional record < 256 ^ N.of_nat 8)%N /\
      (orig_client_order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (cl_msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time record) ++
      encode_uint_le 4 (execution_within_firm_short_code record) ++
      encode_uint_le 4 (client_identification_shortcode record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (order_id_optional record) ++
      encode_uint_le 8 (orig_client_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (cl_msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (execution_within_firm_short_code_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_identification_shortcode_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (symbol_index_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (emm_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (order_id_optional_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (orig_client_order_id_value, bytes) =>
                                              Some ({| cl_msg_seq_num := cl_msg_seq_num_value; firm_id := firm_id_value; sending_time := sending_time_value; execution_within_firm_short_code := execution_within_firm_short_code_value; client_identification_shortcode := client_identification_shortcode_value; client_order_id := client_order_id_value; symbol_index := symbol_index_value; emm := emm_value; order_id_optional := order_id_optional_value; orig_client_order_id := orig_client_order_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CollarBreachConfirmationMessage.

  Module PriceInputMessage.

    (** PriceInputMessage *)
    Record t := {
      cl_msg_seq_num : N;
      firm_id : list byte;
      sending_time : N;
      execution_within_firm_short_code : N;
      client_identification_shortcode : N;
      client_order_id : N;
      symbol_index : N;
      emm : N;
      input_price_type : N;
      price_optional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (execution_within_firm_short_code record < 256 ^ N.of_nat 4)%N /\
      (client_identification_shortcode record < 256 ^ N.of_nat 4)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (input_price_type record < 256 ^ N.of_nat 1)%N /\
      (price_optional record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (cl_msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time record) ++
      encode_uint_le 4 (execution_within_firm_short_code record) ++
      encode_uint_le 4 (client_identification_shortcode record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint 1 (input_price_type record) ++
      encode_uint_le 8 (price_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (cl_msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (execution_within_firm_short_code_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_identification_shortcode_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (symbol_index_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (emm_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (input_price_type_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (price_optional_value, bytes) =>
                                              Some ({| cl_msg_seq_num := cl_msg_seq_num_value; firm_id := firm_id_value; sending_time := sending_time_value; execution_within_firm_short_code := execution_within_firm_short_code_value; client_identification_shortcode := client_identification_shortcode_value; client_order_id := client_order_id_value; symbol_index := symbol_index_value; emm := emm_value; input_price_type := input_price_type_value; price_optional := price_optional_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceInputMessage.

  Module LiquidityProviderCommandMessage.

    (** LiquidityProviderCommandMessage *)
    Record t := {
      cl_msg_seq_num : N;
      firm_id : list byte;
      sending_time : N;
      execution_within_firm_short_code : N;
      client_identification_shortcode : N;
      client_order_id : N;
      symbol_index : N;
      emm : N;
      lp_action_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (execution_within_firm_short_code record < 256 ^ N.of_nat 4)%N /\
      (client_identification_shortcode record < 256 ^ N.of_nat 4)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (lp_action_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (cl_msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time record) ++
      encode_uint_le 4 (execution_within_firm_short_code record) ++
      encode_uint_le 4 (client_identification_shortcode record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint 1 (lp_action_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (cl_msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (execution_within_firm_short_code_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_identification_shortcode_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (symbol_index_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (emm_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (lp_action_code_value, bytes) =>
                                          Some ({| cl_msg_seq_num := cl_msg_seq_num_value; firm_id := firm_id_value; sending_time := sending_time_value; execution_within_firm_short_code := execution_within_firm_short_code_value; client_identification_shortcode := client_identification_shortcode_value; client_order_id := client_order_id_value; symbol_index := symbol_index_value; emm := emm_value; lp_action_code := lp_action_code_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LiquidityProviderCommandMessage.

  Module AskForQuoteMessage.

    (** AskForQuoteMessage *)
    Record t := {
      msg_seq_num : N;
      firm_id : list byte;
      symbol_index : N;
      emm : N;
      afq_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (afq_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint 1 (afq_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (symbol_index_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (emm_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (afq_reason_value, bytes) =>
                          Some ({| msg_seq_num := msg_seq_num_value; firm_id := firm_id_value; symbol_index := symbol_index_value; emm := emm_value; afq_reason := afq_reason_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskForQuoteMessage.

  Module RequestForExecutionMessage.

    (** RequestForExecutionMessage *)
    Record t := {
      msg_seq_num : N;
      firm_id : list byte;
      symbol_index : N;
      emm : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (symbol_index_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (emm_value, bytes) =>
                      Some ({| msg_seq_num := msg_seq_num_value; firm_id := firm_id_value; symbol_index := symbol_index_value; emm := emm_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RequestForExecutionMessage.

  Module RfqNotificationMessage.

    (** RFQNotificationMessage *)
    Record t := {
      msg_seq_num : N;
      firm_id : list byte;
      book_in : N;
      book_out_time_optional : N;
      oeg_in_from_me_optional : N;
      oeg_out_to_member_optional : N;
      quote_req_id : N;
      order_qty : N;
      counterpart_firm_id : list byte;
      symbol_index : N;
      emm : N;
      rfq_update_type : N;
      side_optional : N;
      end_client : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (book_out_time_optional record < 256 ^ N.of_nat 8)%N /\
      (oeg_in_from_me_optional record < 256 ^ N.of_nat 8)%N /\
      (oeg_out_to_member_optional record < 256 ^ N.of_nat 8)%N /\
      (quote_req_id record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (counterpart_firm_id record) = 8 /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (rfq_update_type record < 256 ^ N.of_nat 1)%N /\
      (side_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (end_client record) = 11.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (book_out_time_optional record) ++
      encode_uint_le 8 (oeg_in_from_me_optional record) ++
      encode_uint_le 8 (oeg_out_to_member_optional record) ++
      encode_uint_le 8 (quote_req_id record) ++
      encode_uint_le 8 (order_qty record) ++
      encode_bytes 8 (counterpart_firm_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint 1 (rfq_update_type record) ++
      encode_uint 1 (side_optional record) ++
      encode_bytes 11 (end_client record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (book_in_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (book_out_time_optional_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (oeg_in_from_me_optional_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (oeg_out_to_member_optional_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (quote_req_id_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (order_qty_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (counterpart_firm_id_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (symbol_index_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (emm_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (rfq_update_type_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (side_optional_value, bytes) =>
                                                          match decode_bytes 11 bytes with
                                                          | None => None
                                                          | Some (end_client_value, bytes) =>
                                                              Some ({| msg_seq_num := msg_seq_num_value; firm_id := firm_id_value; book_in := book_in_value; book_out_time_optional := book_out_time_optional_value; oeg_in_from_me_optional := oeg_in_from_me_optional_value; oeg_out_to_member_optional := oeg_out_to_member_optional_value; quote_req_id := quote_req_id_value; order_qty := order_qty_value; counterpart_firm_id := counterpart_firm_id_value; symbol_index := symbol_index_value; emm := emm_value; rfq_update_type := rfq_update_type_value; side_optional := side_optional_value; end_client := end_client_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 86.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RfqNotificationMessage.

  Module RfqMatchingStatusMessage.

    (** RFQMatchingStatusMessage *)
    Record t := {
      msg_seq_num : N;
      firm_id : list byte;
      book_in : N;
      book_out_time_optional : N;
      oeg_in_from_me_optional : N;
      oeg_out_to_member_optional : N;
      quote_req_id : N;
      potential_matching_px : N;
      potential_matching_qty : N;
      symbol_index : N;
      emm : N;
      side : N;
      number_of_lps : N;
      recipient_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (book_out_time_optional record < 256 ^ N.of_nat 8)%N /\
      (oeg_in_from_me_optional record < 256 ^ N.of_nat 8)%N /\
      (oeg_out_to_member_optional record < 256 ^ N.of_nat 8)%N /\
      (quote_req_id record < 256 ^ N.of_nat 8)%N /\
      (potential_matching_px record < 256 ^ N.of_nat 8)%N /\
      (potential_matching_qty record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (number_of_lps record < 256 ^ N.of_nat 1)%N /\
      (recipient_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (book_out_time_optional record) ++
      encode_uint_le 8 (oeg_in_from_me_optional record) ++
      encode_uint_le 8 (oeg_out_to_member_optional record) ++
      encode_uint_le 8 (quote_req_id record) ++
      encode_uint_le 8 (potential_matching_px record) ++
      encode_uint_le 8 (potential_matching_qty record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint 1 (side record) ++
      encode_uint 1 (number_of_lps record) ++
      encode_uint 1 (recipient_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (book_in_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (book_out_time_optional_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (oeg_in_from_me_optional_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (oeg_out_to_member_optional_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (quote_req_id_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (potential_matching_px_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (potential_matching_qty_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (symbol_index_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (emm_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (side_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (number_of_lps_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (recipient_type_value, bytes) =>
                                                              Some ({| msg_seq_num := msg_seq_num_value; firm_id := firm_id_value; book_in := book_in_value; book_out_time_optional := book_out_time_optional_value; oeg_in_from_me_optional := oeg_in_from_me_optional_value; oeg_out_to_member_optional := oeg_out_to_member_optional_value; quote_req_id := quote_req_id_value; potential_matching_px := potential_matching_px_value; potential_matching_qty := potential_matching_qty_value; symbol_index := symbol_index_value; emm := emm_value; side := side_value; number_of_lps := number_of_lps_value; recipient_type := recipient_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RfqMatchingStatusMessage.

  Module UserNotificationMessage.

    (** UserNotificationMessage *)
    Record t := {
      msg_seq_num : N;
      firm_id : list byte;
      execution_within_firm_short_code_optional : N;
      client_identification_shortcode : N;
      family_id : list byte;
      symbol_index_optional : N;
      user_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (execution_within_firm_short_code_optional record < 256 ^ N.of_nat 4)%N /\
      (client_identification_shortcode record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (family_id record) = 8 /\
      (symbol_index_optional record < 256 ^ N.of_nat 4)%N /\
      (user_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 4 (execution_within_firm_short_code_optional record) ++
      encode_uint_le 4 (client_identification_shortcode record) ++
      encode_bytes 8 (family_id record) ++
      encode_uint_le 4 (symbol_index_optional record) ++
      encode_uint 1 (user_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (execution_within_firm_short_code_optional_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (client_identification_shortcode_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (family_id_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (symbol_index_optional_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (user_status_value, bytes) =>
                                  Some ({| msg_seq_num := msg_seq_num_value; firm_id := firm_id_value; execution_within_firm_short_code_optional := execution_within_firm_short_code_optional_value; client_identification_shortcode := client_identification_shortcode_value; family_id := family_id_value; symbol_index_optional := symbol_index_optional_value; user_status := user_status_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UserNotificationMessage.

  Module DeclarationCancelAndRefusalMessage.

    (** DeclarationCancelAndRefusalMessage *)
    Record t := {
      cl_msg_seq_num : N;
      firm_id : list byte;
      sending_time : N;
      client_order_id : N;
      symbol_index : N;
      emm : N;
      declaration_id : N;
      action_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (declaration_id record < 256 ^ N.of_nat 8)%N /\
      (action_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (cl_msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (declaration_id record) ++
      encode_uint 1 (action_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (cl_msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (client_order_id_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (symbol_index_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (emm_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (declaration_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (action_type_value, bytes) =>
                                      Some ({| cl_msg_seq_num := cl_msg_seq_num_value; firm_id := firm_id_value; sending_time := sending_time_value; client_order_id := client_order_id_value; symbol_index := symbol_index_value; emm := emm_value; declaration_id := declaration_id_value; action_type := action_type_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DeclarationCancelAndRefusalMessage.

  Module FundPriceInputMessage.

    (** FundPriceInputMessage *)
    Record t := {
      cl_msg_seq_num : N;
      firm_id : list byte;
      sending_time : N;
      client_order_id : N;
      symbol_index : N;
      emm : N;
      price : N;
      bypass_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (bypass_indicator record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (cl_msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (sending_time record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (price record) ++
      encode_uint 1 (bypass_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (cl_msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (client_order_id_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (symbol_index_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (emm_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (bypass_indicator_value, bytes) =>
                                      Some ({| cl_msg_seq_num := cl_msg_seq_num_value; firm_id := firm_id_value; sending_time := sending_time_value; client_order_id := client_order_id_value; symbol_index := symbol_index_value; emm := emm_value; price := price_value; bypass_indicator := bypass_indicator_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FundPriceInputMessage.

  Module FundPriceInputAckMessage.

    (** FundPriceInputAckMessage *)
    Record t := {
      msg_seq_num : N;
      firm_id : list byte;
      client_order_id : N;
      symbol_index : N;
      emm : N;
      price : N;
      bypass_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (bypass_indicator record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (price record) ++
      encode_uint 1 (bypass_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (symbol_index_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (emm_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (bypass_indicator_value, bytes) =>
                                  Some ({| msg_seq_num := msg_seq_num_value; firm_id := firm_id_value; client_order_id := client_order_id_value; symbol_index := symbol_index_value; emm := emm_value; price := price_value; bypass_indicator := bypass_indicator_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FundPriceInputAckMessage.

  Module DeclarationEntryRejectMessage.

    (** DeclarationEntryRejectMessage *)
    Record t := {
      msg_seq_num : N;
      firm_id : list byte;
      client_order_id : N;
      symbol_index : N;
      emm_optional : N;
      mi_cof_secondary_listing : list byte;
      operation_type : N;
      error_code : N;
      rejected_message : N;
      rejected_message_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (mi_cof_secondary_listing record) = 4 /\
      (operation_type record < 256 ^ N.of_nat 1)%N /\
      (error_code record < 256 ^ N.of_nat 2)%N /\
      (rejected_message record < 256 ^ N.of_nat 1)%N /\
      (rejected_message_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm_optional record) ++
      encode_bytes 4 (mi_cof_secondary_listing record) ++
      encode_uint 1 (operation_type record) ++
      encode_uint_le 2 (error_code record) ++
      encode_uint 1 (rejected_message record) ++
      encode_uint_le 2 (rejected_message_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (symbol_index_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (emm_optional_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (mi_cof_secondary_listing_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (operation_type_value, bytes) =>
                                  match decode_uint_le 2 bytes with
                                  | None => None
                                  | Some (error_code_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (rejected_message_value, bytes) =>
                                          match decode_uint_le 2 bytes with
                                          | None => None
                                          | Some (rejected_message_id_value, bytes) =>
                                              Some ({| msg_seq_num := msg_seq_num_value; firm_id := firm_id_value; client_order_id := client_order_id_value; symbol_index := symbol_index_value; emm_optional := emm_optional_value; mi_cof_secondary_listing := mi_cof_secondary_listing_value; operation_type := operation_type_value; error_code := error_code_value; rejected_message := rejected_message_value; rejected_message_id := rejected_message_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DeclarationEntryRejectMessage.

  Module SynchronizationTimeMessage.

    (** SynchronizationTimeMessage *)
    Record t := {
      msg_seq_num : N;
      oeg_out_to_member_optional : N;
      resynchronization_id : N;
      last_book_in_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (oeg_out_to_member_optional record < 256 ^ N.of_nat 8)%N /\
      (resynchronization_id record < 256 ^ N.of_nat 2)%N /\
      (last_book_in_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_uint_le 8 (oeg_out_to_member_optional record) ++
      encode_uint_le 2 (resynchronization_id record) ++
      encode_uint_le 8 (last_book_in_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (oeg_out_to_member_optional_value, bytes) =>
              match decode_uint_le 2 bytes with
              | None => None
              | Some (resynchronization_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (last_book_in_time_value, bytes) =>
                      Some ({| msg_seq_num := msg_seq_num_value; oeg_out_to_member_optional := oeg_out_to_member_optional_value; resynchronization_id := resynchronization_id_value; last_book_in_time := last_book_in_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SynchronizationTimeMessage.

  Module LogonMessage.

    (** LogonMessage *)
    Record t := {
      logical_access_id : N;
      oe_partition_id : N;
      last_msg_seq_num_optional : N;
      software_provider : list byte;
      queueing_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (logical_access_id record < 256 ^ N.of_nat 4)%N /\
      (oe_partition_id record < 256 ^ N.of_nat 2)%N /\
      (last_msg_seq_num_optional record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (software_provider record) = 8 /\
      (queueing_indicator record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (logical_access_id record) ++
      encode_uint_le 2 (oe_partition_id record) ++
      encode_uint_le 4 (last_msg_seq_num_optional record) ++
      encode_bytes 8 (software_provider record) ++
      encode_uint 1 (queueing_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (logical_access_id_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (oe_partition_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (last_msg_seq_num_optional_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (software_provider_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (queueing_indicator_value, bytes) =>
                          Some ({| logical_access_id := logical_access_id_value; oe_partition_id := oe_partition_id_value; last_msg_seq_num_optional := last_msg_seq_num_optional_value; software_provider := software_provider_value; queueing_indicator := queueing_indicator_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonMessage.

  Module LogonAckMessage.

    (** LogonAckMessage *)
    Record t := {
      exchange_id : list byte;
      last_cl_msg_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 8 /\
      (last_cl_msg_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (exchange_id record) ++
      encode_uint_le 4 (last_cl_msg_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (last_cl_msg_seq_num_value, bytes) =>
              Some ({| exchange_id := exchange_id_value; last_cl_msg_seq_num := last_cl_msg_seq_num_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonAckMessage.

  Module LogonRejectMessage.

    (** LogonRejectMessage *)
    Record t := {
      exchange_id : list byte;
      logon_reject_code : N;
      last_cl_msg_seq_num : N;
      last_msg_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 8 /\
      (logon_reject_code record < 256 ^ N.of_nat 1)%N /\
      (last_cl_msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_msg_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (exchange_id record) ++
      encode_uint 1 (logon_reject_code record) ++
      encode_uint_le 4 (last_cl_msg_seq_num record) ++
      encode_uint_le 4 (last_msg_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (logon_reject_code_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (last_cl_msg_seq_num_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (last_msg_seq_num_value, bytes) =>
                      Some ({| exchange_id := exchange_id_value; logon_reject_code := logon_reject_code_value; last_cl_msg_seq_num := last_cl_msg_seq_num_value; last_msg_seq_num := last_msg_seq_num_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonRejectMessage.

  Module LogoutMessage.

    (** LogoutMessage *)
    Record t := {
      log_out_reason_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (log_out_reason_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (log_out_reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (log_out_reason_code_value, bytes) =>
          Some ({| log_out_reason_code := log_out_reason_code_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End LogoutMessage.

  Module TechnicalRejectMessage.

    (** TechnicalRejectMessage *)
    Record t := {
      oeg_out_to_member_optional : N;
      rejected_client_message_sequence_number : N;
      rejected_message : N;
      error_code : N;
      rejected_message_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (oeg_out_to_member_optional record < 256 ^ N.of_nat 8)%N /\
      (rejected_client_message_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (rejected_message record < 256 ^ N.of_nat 1)%N /\
      (error_code record < 256 ^ N.of_nat 2)%N /\
      (rejected_message_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (oeg_out_to_member_optional record) ++
      encode_uint_le 4 (rejected_client_message_sequence_number record) ++
      encode_uint 1 (rejected_message record) ++
      encode_uint_le 2 (error_code record) ++
      encode_uint_le 2 (rejected_message_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (oeg_out_to_member_optional_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (rejected_client_message_sequence_number_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (rejected_message_value, bytes) =>
                  match decode_uint_le 2 bytes with
                  | None => None
                  | Some (error_code_value, bytes) =>
                      match decode_uint_le 2 bytes with
                      | None => None
                      | Some (rejected_message_id_value, bytes) =>
                          Some ({| oeg_out_to_member_optional := oeg_out_to_member_optional_value; rejected_client_message_sequence_number := rejected_client_message_sequence_number_value; rejected_message := rejected_message_value; error_code := error_code_value; rejected_message_id := rejected_message_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TechnicalRejectMessage.

End EuronextOptiqOrderEntryGatewayV13.
