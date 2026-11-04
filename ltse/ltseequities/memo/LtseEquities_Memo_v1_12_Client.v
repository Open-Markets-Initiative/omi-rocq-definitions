From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Long-Term Stock Exchange Members Orders

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
      - a field read in bits
      - a block whose stated length holds more than its fields

    License: MIT No Attribution
  *)

Module LtseEquitiesMemoV112Client.

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

    (** Ltse Tcp Login message *)
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

    (** Ltse Tcp Replay Request message *)
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

    (** Ltse Tcp Replay All Request message *)
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

    (** Ltse Tcp Stream Request message *)
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

  Module OrderCancelReplaceRequestMessage.

    (** OrderCancelReplaceRequestMessage *)
    Record t := {
      orig_cl_ord_id : list byte;
      cl_ord_id : list byte;
      symbol : list byte;
      symbol_sfx : list byte;
      side : list byte;
      order_qty : N;
      ord_type : list byte;
      price : N;
      display_qty : N;
      locate_reqd : list byte;
      link_id_optional : list byte;
      locate_broker_optional : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig_cl_ord_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (symbol_sfx record) = 6 /\
      Datatypes.length (side record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (locate_reqd record) = 1 /\
      Datatypes.length (link_id_optional record) = 4 /\
      Datatypes.length (locate_broker_optional record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (orig_cl_ord_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 6 (symbol_sfx record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_bytes 1 (locate_reqd record) ++
      encode_bytes 4 (link_id_optional record) ++
      encode_bytes 4 (locate_broker_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (orig_cl_ord_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (symbol_sfx_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_qty_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (ord_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (display_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (locate_reqd_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (link_id_optional_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (locate_broker_optional_value, bytes) =>
                                                      Some ({| orig_cl_ord_id := orig_cl_ord_id_value; cl_ord_id := cl_ord_id_value; symbol := symbol_value; symbol_sfx := symbol_sfx_value; side := side_value; order_qty := order_qty_value; ord_type := ord_type_value; price := price_value; display_qty := display_qty_value; locate_reqd := locate_reqd_value; link_id_optional := link_id_optional_value; locate_broker_optional := locate_broker_optional_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelReplaceRequestMessage.

  Module OrderCancelRequestMessage.

    (** OrderCancelRequestMessage *)
    Record t := {
      orig_cl_ord_id_optional : list byte;
      order_id_optional : N;
      cl_ord_id : list byte;
      symbol : list byte;
      symbol_sfx : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig_cl_ord_id_optional record) = 16 /\
      (order_id_optional record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (symbol_sfx record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (orig_cl_ord_id_optional record) ++
      encode_uint 8 (order_id_optional record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 6 (symbol_sfx record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (orig_cl_ord_id_optional_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_optional_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (symbol_sfx_value, bytes) =>
                          Some ({| orig_cl_ord_id_optional := orig_cl_ord_id_optional_value; order_id_optional := order_id_optional_value; cl_ord_id := cl_ord_id_value; symbol := symbol_value; symbol_sfx := symbol_sfx_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelRequestMessage.

  Module MassCancelRequestMessage.

    (** MassCancelRequestMessage *)
    Record t := {
      cl_ord_id : list byte;
      symbol : list byte;
      symbol_sfx : list byte;
      side_optional : list byte;
      lower_than_price : N;
      higher_than_price : N;
      cancel_group_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (symbol_sfx record) = 6 /\
      Datatypes.length (side_optional record) = 1 /\
      (lower_than_price record < 256 ^ N.of_nat 8)%N /\
      (higher_than_price record < 256 ^ N.of_nat 8)%N /\
      (cancel_group_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 6 (symbol_sfx record) ++
      encode_bytes 1 (side_optional record) ++
      encode_uint 8 (lower_than_price record) ++
      encode_uint 8 (higher_than_price record) ++
      encode_uint 2 (cancel_group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (symbol_sfx_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_optional_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (lower_than_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (higher_than_price_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (cancel_group_id_value, bytes) =>
                                  Some ({| cl_ord_id := cl_ord_id_value; symbol := symbol_value; symbol_sfx := symbol_sfx_value; side_optional := side_optional_value; lower_than_price := lower_than_price_value; higher_than_price := higher_than_price_value; cancel_group_id := cancel_group_id_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelRequestMessage.

End LtseEquitiesMemoV112Client.
