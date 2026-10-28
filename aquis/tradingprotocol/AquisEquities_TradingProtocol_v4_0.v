From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Aquis Exchange Aquis Trading Protocol

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
  *)

Module AquisEquitiesTradingProtocolV40.

  Module MessageHeader.

    (** Aquis Atp message header *)
    Record t := {
      msg_length : N;
      msg_type : N;
      msg_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_length record < 256 ^ N.of_nat 2)%N /\
      (msg_type record < 256 ^ N.of_nat 1)%N /\
      (msg_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_length record) ++
      encode_uint 1 (msg_type record) ++
      encode_uint 4 (msg_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_no_value, bytes) =>
                  Some ({| msg_length := msg_length_value; msg_type := msg_type_value; msg_seq_no := msg_seq_no_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End MessageHeader.

  Module LoginMessage.

    (** The Login message is sent by the trading Member as the initial message used to establish a trading session *)
    Record t := {
      protocol_version : N;
      sender_id : list byte;
      password : list byte;
      inactivity_timeout : N;
      atp_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (protocol_version record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sender_id record) = 16 /\
      Datatypes.length (password record) = 16 /\
      (inactivity_timeout record < 256 ^ N.of_nat 2)%N /\
      (atp_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (protocol_version record) ++
      encode_bytes 16 (sender_id record) ++
      encode_bytes 16 (password record) ++
      encode_uint 2 (inactivity_timeout record) ++
      encode_uint 4 (atp_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (protocol_version_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (sender_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (password_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (inactivity_timeout_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (atp_seq_no_value, bytes) =>
                          Some ({| protocol_version := protocol_version_value; sender_id := sender_id_value; password := password_value; inactivity_timeout := inactivity_timeout_value; atp_seq_no := atp_seq_no_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginMessage.

  Module LoginResponseMessage.

    (** The Login Response message is sent by Aquis to acknowledge a Login request, and either accept or reject it. *)
    Record t := {
      result_code : N;
      client_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (result_code record < 256 ^ N.of_nat 1)%N /\
      (client_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (result_code record) ++
      encode_uint 4 (client_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (result_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (client_seq_no_value, bytes) =>
              Some ({| result_code := result_code_value; client_seq_no := client_seq_no_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End LoginResponseMessage.

  Module LogoutMessage.

    (** The Logout message is usually sent as a response to the Logout Request. The TCP/IP connection is closed immediately after this message has been sent. *)
    Record t := {
      logout_reason_code : N;
      reason_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (logout_reason_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reason_text record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (logout_reason_code record) ++
      encode_bytes 32 (reason_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (logout_reason_code_value, bytes) =>
          match decode_bytes 32 bytes with
          | None => None
          | Some (reason_text_value, bytes) =>
              Some ({| logout_reason_code := logout_reason_code_value; reason_text := reason_text_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogoutMessage.

  Module IcebergOrderRefreshMessage.

    (** Aquis sends an Iceberg Order Refresh message to notify the Member when an iceberg order is refreshed from the non-displayed reserve quantity. *)
    Record t := {
      order_ref : N;
      orig_aqx_ord_id : N;
      new_aqx_ord_id : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (orig_aqx_ord_id record < 256 ^ N.of_nat 4)%N /\
      (new_aqx_ord_id record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (order_ref record) ++
      encode_uint 4 (orig_aqx_ord_id record) ++
      encode_uint 4 (new_aqx_ord_id record) ++
      encode_uint 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (order_ref_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orig_aqx_ord_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (new_aqx_ord_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      Some ({| order_ref := order_ref_value; orig_aqx_ord_id := orig_aqx_ord_id_value; new_aqx_ord_id := new_aqx_ord_id_value; quantity := quantity_value |}, bytes)
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

  End IcebergOrderRefreshMessage.

  Module TradeBustMessage.

    (** If a trade is invalidated, a Trade Bust message is sent to notify the trading Member. *)
    Record t := {
      order_ref : N;
      quantity : N;
      price : N;
      side : N;
      trade_ref : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (trade_ref record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (order_ref record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (trade_ref record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (order_ref_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (quantity_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_ref_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (timestamp_value, bytes) =>
                              Some ({| order_ref := order_ref_value; quantity := quantity_value; price := price_value; side := side_value; trade_ref := trade_ref_value; timestamp := timestamp_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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

  End TradeBustMessage.

  Module IoiInviteMessage.

    (** Message from Aquis to the member indicating a firm up invite. The invite will expire 300ms after the value in the timestamp field. *)
    Record t := {
      order_ref : N;
      price : N;
      quantity : N;
      min_qty : N;
      timestamp : N;
      user_tag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (user_tag record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (order_ref record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (min_qty record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (user_tag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (order_ref_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (min_qty_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (user_tag_value, bytes) =>
                              Some ({| order_ref := order_ref_value; price := price_value; quantity := quantity_value; min_qty := min_qty_value; timestamp := timestamp_value; user_tag := user_tag_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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

  End IoiInviteMessage.

  Module IoiFirmupMessage.

    (** Firm up message to be used as a response to an invite. *)
    Record t := {
      order_ref : N;
      price : N;
      quantity : N;
      min_qty : N;
      user_tag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      (user_tag record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (order_ref record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (min_qty record) ++
      encode_uint 8 (user_tag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (order_ref_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (min_qty_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (user_tag_value, bytes) =>
                          Some ({| order_ref := order_ref_value; price := price_value; quantity := quantity_value; min_qty := min_qty_value; user_tag := user_tag_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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

  End IoiFirmupMessage.

End AquisEquitiesTradingProtocolV40.
