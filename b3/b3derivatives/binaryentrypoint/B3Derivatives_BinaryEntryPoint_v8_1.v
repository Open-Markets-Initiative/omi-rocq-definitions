From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Brasil, Bolsa, Balcão Binary Entry Point

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
      - a block whose stated length holds more than its fields
      - a Composite rule
      - a run counted by a field
  *)

Module B3DerivativesBinaryEntryPointV81.

  Module SimpleOpenFramingHeader.

    (** Simple Open Framing Header *)
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

  End SimpleOpenFramingHeader.

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

  Module InboundBusinessHeader.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InboundBusinessHeader.

  Module InvestorId.

    (** SimpleNewOrderMessage *)
    Record t := {
      prefix : N;
      offset_2_padding_2 : N;
      document : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prefix record < 256 ^ N.of_nat 2)%N /\
      (offset_2_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (document record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (prefix record) ++
      encode_uint 2 (offset_2_padding_2 record) ++
      encode_uint 4 (document record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (prefix_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_2_padding_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (document_value, bytes) =>
                  Some ({| prefix := prefix_value; offset_2_padding_2 := offset_2_padding_2_value; document := document_value |}, bytes)
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

  End InvestorId.

  Module InboundBusinessHeader2.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InboundBusinessHeader2.

  Module InvestorId2.

    (** SimpleNewOrderMessage *)
    Record t := {
      prefix : N;
      offset_2_padding_2 : N;
      document : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prefix record < 256 ^ N.of_nat 2)%N /\
      (offset_2_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (document record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (prefix record) ++
      encode_uint 2 (offset_2_padding_2 record) ++
      encode_uint 4 (document record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (prefix_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_2_padding_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (document_value, bytes) =>
                  Some ({| prefix := prefix_value; offset_2_padding_2 := offset_2_padding_2_value; document := document_value |}, bytes)
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

  End InvestorId2.

  Module InboundBusinessHeader3.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InboundBusinessHeader3.

  Module CustodianInfo.

    (** NewOrderSingleMessage *)
    Record t := {
      custodian : N;
      custody_account : N;
      custody_allocation_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (custodian record < 256 ^ N.of_nat 4)%N /\
      (custody_account record < 256 ^ N.of_nat 4)%N /\
      (custody_allocation_type record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (custodian record) ++
      encode_uint 4 (custody_account record) ++
      encode_uint 4 (custody_allocation_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (custodian_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (custody_account_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (custody_allocation_type_value, bytes) =>
                  Some ({| custodian := custodian_value; custody_account := custody_account_value; custody_allocation_type := custody_allocation_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End CustodianInfo.

  Module InvestorId3.

    (** SimpleNewOrderMessage *)
    Record t := {
      prefix : N;
      offset_2_padding_2 : N;
      document : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prefix record < 256 ^ N.of_nat 2)%N /\
      (offset_2_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (document record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (prefix record) ++
      encode_uint 2 (offset_2_padding_2 record) ++
      encode_uint 4 (document record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (prefix_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_2_padding_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (document_value, bytes) =>
                  Some ({| prefix := prefix_value; offset_2_padding_2 := offset_2_padding_2_value; document := document_value |}, bytes)
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

  End InvestorId3.

  Module InboundBusinessHeader4.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InboundBusinessHeader4.

  Module CustodianInfo2.

    (** NewOrderSingleMessage *)
    Record t := {
      custodian : N;
      custody_account : N;
      custody_allocation_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (custodian record < 256 ^ N.of_nat 4)%N /\
      (custody_account record < 256 ^ N.of_nat 4)%N /\
      (custody_allocation_type record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (custodian record) ++
      encode_uint 4 (custody_account record) ++
      encode_uint 4 (custody_allocation_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (custodian_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (custody_account_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (custody_allocation_type_value, bytes) =>
                  Some ({| custodian := custodian_value; custody_account := custody_account_value; custody_allocation_type := custody_allocation_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End CustodianInfo2.

  Module InvestorId4.

    (** SimpleNewOrderMessage *)
    Record t := {
      prefix : N;
      offset_2_padding_2 : N;
      document : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prefix record < 256 ^ N.of_nat 2)%N /\
      (offset_2_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (document record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (prefix record) ++
      encode_uint 2 (offset_2_padding_2 record) ++
      encode_uint 4 (document record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (prefix_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_2_padding_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (document_value, bytes) =>
                  Some ({| prefix := prefix_value; offset_2_padding_2 := offset_2_padding_2_value; document := document_value |}, bytes)
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

  End InvestorId4.

  Module InboundBusinessHeader5.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InboundBusinessHeader5.

  Module InboundBusinessHeader6.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InboundBusinessHeader6.

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

  Module OutboundBusinessHeader.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutboundBusinessHeader.

  Module InvestorId5.

    (** SimpleNewOrderMessage *)
    Record t := {
      prefix : N;
      offset_2_padding_2 : N;
      document : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prefix record < 256 ^ N.of_nat 2)%N /\
      (offset_2_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (document record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (prefix record) ++
      encode_uint 2 (offset_2_padding_2 record) ++
      encode_uint 4 (document record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (prefix_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_2_padding_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (document_value, bytes) =>
                  Some ({| prefix := prefix_value; offset_2_padding_2 := offset_2_padding_2_value; document := document_value |}, bytes)
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

  End InvestorId5.

  Module OutboundBusinessHeader2.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutboundBusinessHeader2.

  Module InvestorId6.

    (** SimpleNewOrderMessage *)
    Record t := {
      prefix : N;
      offset_2_padding_2 : N;
      document : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prefix record < 256 ^ N.of_nat 2)%N /\
      (offset_2_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (document record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (prefix record) ++
      encode_uint 2 (offset_2_padding_2 record) ++
      encode_uint 4 (document record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (prefix_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_2_padding_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (document_value, bytes) =>
                  Some ({| prefix := prefix_value; offset_2_padding_2 := offset_2_padding_2_value; document := document_value |}, bytes)
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

  End InvestorId6.

  Module OutboundBusinessHeader3.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutboundBusinessHeader3.

  Module InvestorId7.

    (** SimpleNewOrderMessage *)
    Record t := {
      prefix : N;
      offset_2_padding_2 : N;
      document : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prefix record < 256 ^ N.of_nat 2)%N /\
      (offset_2_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (document record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (prefix record) ++
      encode_uint 2 (offset_2_padding_2 record) ++
      encode_uint 4 (document record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (prefix_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_2_padding_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (document_value, bytes) =>
                  Some ({| prefix := prefix_value; offset_2_padding_2 := offset_2_padding_2_value; document := document_value |}, bytes)
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

  End InvestorId7.

  Module OutboundBusinessHeader4.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutboundBusinessHeader4.

  Module OutboundBusinessHeader5.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutboundBusinessHeader5.

  Module InvestorId8.

    (** SimpleNewOrderMessage *)
    Record t := {
      prefix : N;
      offset_2_padding_2 : N;
      document : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prefix record < 256 ^ N.of_nat 2)%N /\
      (offset_2_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (document record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (prefix record) ++
      encode_uint 2 (offset_2_padding_2 record) ++
      encode_uint 4 (document record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (prefix_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_2_padding_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (document_value, bytes) =>
                  Some ({| prefix := prefix_value; offset_2_padding_2 := offset_2_padding_2_value; document := document_value |}, bytes)
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

  End InvestorId8.

  Module OutboundBusinessHeader6.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutboundBusinessHeader6.

  Module OutboundBusinessHeader7.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutboundBusinessHeader7.

  Module InboundBusinessHeader7.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InboundBusinessHeader7.

  Module GroupSizeEncoding2.

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

  End GroupSizeEncoding2.

  Module OutboundBusinessHeader8.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutboundBusinessHeader8.

  Module BidirectionalBusinessHeader.

    (** BidirectionalBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      market_segment_id_optional : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      (market_segment_id_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_uint 1 (market_segment_id_optional record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (market_segment_id_optional_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (padding_value, bytes) =>
                              Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; market_segment_id_optional := market_segment_id_optional_value; padding := padding_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidirectionalBusinessHeader.

  Module GroupSizeEncoding3.

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

  End GroupSizeEncoding3.

  Module BidirectionalBusinessHeader2.

    (** BidirectionalBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      market_segment_id_optional : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      (market_segment_id_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_uint 1 (market_segment_id_optional record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (market_segment_id_optional_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (padding_value, bytes) =>
                              Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; market_segment_id_optional := market_segment_id_optional_value; padding := padding_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidirectionalBusinessHeader2.

  Module BidirectionalBusinessHeader3.

    (** BidirectionalBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      market_segment_id_optional : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      (market_segment_id_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_uint 1 (market_segment_id_optional record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (market_segment_id_optional_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (padding_value, bytes) =>
                              Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; market_segment_id_optional := market_segment_id_optional_value; padding := padding_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidirectionalBusinessHeader3.

  Module BidirectionalBusinessHeader4.

    (** BidirectionalBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      market_segment_id_optional : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      (market_segment_id_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_uint 1 (market_segment_id_optional record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (market_segment_id_optional_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (padding_value, bytes) =>
                              Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; market_segment_id_optional := market_segment_id_optional_value; padding := padding_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidirectionalBusinessHeader4.

  Module BidirectionalBusinessHeader5.

    (** BidirectionalBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      market_segment_id_optional : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      (market_segment_id_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_uint 1 (market_segment_id_optional record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (market_segment_id_optional_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (padding_value, bytes) =>
                              Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; market_segment_id_optional := market_segment_id_optional_value; padding := padding_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidirectionalBusinessHeader5.

  Module GroupSizeEncoding4.

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

  End GroupSizeEncoding4.

  Module InboundBusinessHeader8.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InboundBusinessHeader8.

  Module InboundBusinessHeader9.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InboundBusinessHeader9.

  Module OutboundBusinessHeader9.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutboundBusinessHeader9.

  Module GroupSizeEncoding5.

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

  End GroupSizeEncoding5.

  Module InboundBusinessHeader10.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InboundBusinessHeader10.

  Module OutboundBusinessHeader10.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutboundBusinessHeader10.

  Module InboundBusinessHeader11.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InboundBusinessHeader11.

  Module InvestorId9.

    (** SimpleNewOrderMessage *)
    Record t := {
      prefix : N;
      offset_2_padding_2 : N;
      document : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prefix record < 256 ^ N.of_nat 2)%N /\
      (offset_2_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (document record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (prefix record) ++
      encode_uint 2 (offset_2_padding_2 record) ++
      encode_uint 4 (document record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (prefix_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_2_padding_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (document_value, bytes) =>
                  Some ({| prefix := prefix_value; offset_2_padding_2 := offset_2_padding_2_value; document := document_value |}, bytes)
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

  End InvestorId9.

  Module OutboundBusinessHeader11.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutboundBusinessHeader11.

  Module InvestorId10.

    (** SimpleNewOrderMessage *)
    Record t := {
      prefix : N;
      offset_2_padding_2 : N;
      document : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prefix record < 256 ^ N.of_nat 2)%N /\
      (offset_2_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (document record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (prefix record) ++
      encode_uint 2 (offset_2_padding_2 record) ++
      encode_uint 4 (document record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (prefix_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_2_padding_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (document_value, bytes) =>
                  Some ({| prefix := prefix_value; offset_2_padding_2 := offset_2_padding_2_value; document := document_value |}, bytes)
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

  End InvestorId10.

End B3DerivativesBinaryEntryPointV81.
