From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * A2X Markets A2X Binary Protocol

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
      - the dispatch that chooses a message by its type
      - a field read in bits

    License: MIT No Attribution
  *)

Module A2XEquitiesTradingProtocolV292.

  Module MessageHeader.

    (** A2X Atp message header *)
    Record t := {
      length_ : N;
      msg_type : N;
      msg_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (msg_type record < 256 ^ N.of_nat 1)%N /\
      (msg_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (msg_type record) ++
      encode_uint 4 (msg_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_no_value, bytes) =>
                  Some ({| length_ := length__value; msg_type := msg_type_value; msg_seq_no := msg_seq_no_value |}, bytes)
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

    (** The Login message is the initial message used to establish a trading session. It is also used to re-establish a session after a break. *)
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

    (** The Login Response message is sent by A2X to acknowledge a Login request, and either accept or reject it. *)
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

    (** The Logout message is usually sent as a response to the Logout Request however it may also be sent by A2X in case of a low sequence number or other protocol violation, or for other reasons. The TCP/IP connection is closed immediately after this message has been sent. *)
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

  Module OrderAddMessage.

    (** The Add Order message is sent by the trading Member to enter an order for a particular security. *)
    Record t := {
      security_id_long : N;
      order_type : N;
      time_in_force : N;
      side : N;
      quantity : N;
      price : N;
      order_capacity : N;
      account : N;
      user_tag : N;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id_long record < 256 ^ N.of_nat 4)%N /\
      (order_type record < 256 ^ N.of_nat 1)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_capacity record < 256 ^ N.of_nat 1)%N /\
      (account record < 256 ^ N.of_nat 2)%N /\
      (user_tag record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_id_long record) ++
      encode_uint 1 (order_type record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 1 (order_capacity record) ++
      encode_uint 2 (account record) ++
      encode_uint 8 (user_tag record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_id_long_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (order_type_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (time_in_force_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (order_capacity_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (account_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (user_tag_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (reserved_16_value, bytes) =>
                                              Some ({| security_id_long := security_id_long_value; order_type := order_type_value; time_in_force := time_in_force_value; side := side_value; quantity := quantity_value; price := price_value; order_capacity := order_capacity_value; account := account_value; user_tag := user_tag_value; reserved_16 := reserved_16_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
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
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAddMessage.

  Module OrderAddExtendedMessage.

    (** The Order Add Extended message is sent by the trading Member to enter an order for a particular security with additional attributes. *)
    Record t := {
      security_id_long : N;
      order_type : N;
      time_in_force : N;
      side : N;
      quantity : N;
      price : N;
      order_capacity : N;
      account : N;
      user_tag : N;
      reserved_16 : list byte;
      display_quantity : N;
      min_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id_long record < 256 ^ N.of_nat 4)%N /\
      (order_type record < 256 ^ N.of_nat 1)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_capacity record < 256 ^ N.of_nat 1)%N /\
      (account record < 256 ^ N.of_nat 2)%N /\
      (user_tag record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_16 record) = 16 /\
      (display_quantity record < 256 ^ N.of_nat 4)%N /\
      (min_qty record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_id_long record) ++
      encode_uint 1 (order_type record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 1 (order_capacity record) ++
      encode_uint 2 (account record) ++
      encode_uint 8 (user_tag record) ++
      encode_bytes 16 (reserved_16 record) ++
      encode_uint 4 (display_quantity record) ++
      encode_uint 4 (min_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_id_long_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (order_type_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (time_in_force_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (order_capacity_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (account_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (user_tag_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (reserved_16_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (display_quantity_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (min_qty_value, bytes) =>
                                                      Some ({| security_id_long := security_id_long_value; order_type := order_type_value; time_in_force := time_in_force_value; side := side_value; quantity := quantity_value; price := price_value; order_capacity := order_capacity_value; account := account_value; user_tag := user_tag_value; reserved_16 := reserved_16_value; display_quantity := display_quantity_value; min_qty := min_qty_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 54.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAddExtendedMessage.

  Module OrderCancelMessage.

    (** The Order Cancel message is sent when a user wishes to cancel an open order. *)
    Record t := {
      order_ref : N;
      user_tag : N;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (user_tag record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (order_ref record) ++
      encode_uint 8 (user_tag record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (order_ref_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (user_tag_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (reserved_16_value, bytes) =>
                  Some ({| order_ref := order_ref_value; user_tag := user_tag_value; reserved_16 := reserved_16_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelMessage.

  Module OrderModifyMessage.

    (** The Order Modify message is sent when a user wishes to modify an open order. Order quantity and/or limit price may be modified. Both values must be included, even if one of them is unchanged. *)
    Record t := {
      order_ref : N;
      price : N;
      quantity : N;
      user_tag : N;
      reserved_16 : list byte;
      order_capacity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (user_tag record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_16 record) = 16 /\
      (order_capacity record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (order_ref record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (user_tag record) ++
      encode_bytes 16 (reserved_16 record) ++
      encode_uint 1 (order_capacity record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (user_tag_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (reserved_16_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (order_capacity_value, bytes) =>
                              Some ({| order_ref := order_ref_value; price := price_value; quantity := quantity_value; user_tag := user_tag_value; reserved_16 := reserved_16_value; order_capacity := order_capacity_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderModifyMessage.

  Module OrderModifyExtendedMessage.

    (** The Order Modify Extended message is sent when a user wants to modify an open Order Add Extended. Order quantity and/or limit price and/or display quantity and/or minimum quantity may be modified. All values must be included, even if some are unchanged. *)
    Record t := {
      order_ref : N;
      price : N;
      quantity : N;
      user_tag : N;
      reserved_16 : list byte;
      order_capacity : N;
      display_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (user_tag record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_16 record) = 16 /\
      (order_capacity record < 256 ^ N.of_nat 1)%N /\
      (display_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (order_ref record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (user_tag record) ++
      encode_bytes 16 (reserved_16 record) ++
      encode_uint 1 (order_capacity record) ++
      encode_uint 4 (display_quantity record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (user_tag_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (reserved_16_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (order_capacity_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (display_quantity_value, bytes) =>
                                  Some ({| order_ref := order_ref_value; price := price_value; quantity := quantity_value; user_tag := user_tag_value; reserved_16 := reserved_16_value; order_capacity := order_capacity_value; display_quantity := display_quantity_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderModifyExtendedMessage.

  Module IcebergOrderRefreshMessage.

    (** A2X sends an Iceberg Order Refresh message to notify the Member when an iceberg order is refreshed from the non-displayed reserve quantity. *)
    Record t := {
      order_ref : N;
      orig_a2_x_ord_id : N;
      new_a2_x_ord_id : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (orig_a2_x_ord_id record < 256 ^ N.of_nat 4)%N /\
      (new_a2_x_ord_id record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (order_ref record) ++
      encode_uint 4 (orig_a2_x_ord_id record) ++
      encode_uint 4 (new_a2_x_ord_id record) ++
      encode_uint 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (order_ref_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orig_a2_x_ord_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (new_a2_x_ord_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      Some ({| order_ref := order_ref_value; orig_a2_x_ord_id := orig_a2_x_ord_id_value; new_a2_x_ord_id := new_a2_x_ord_id_value; quantity := quantity_value |}, bytes)
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

  Module TradeCaptureMessage.

    (** A2X uses a Trade Capture Report message for the purpose of allowing members to submit Large in Scale (LS), Negotiated Benchmark Cross (NBC) and Matched Principal (MP) trades to the exchange. *)
    Record t := {
      quantity : N;
      price : N;
      security_id_long : N;
      trade_capture_type : N;
      reserved_1 : list byte;
      user_tag : N;
      reserved_8 : list byte;
      buy_account : N;
      buy_order_capacity : N;
      reserved_long_2 : list byte;
      sell_account : N;
      sell_order_capacity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (security_id_long record < 256 ^ N.of_nat 4)%N /\
      (trade_capture_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reserved_1 record) = 1 /\
      (user_tag record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_8 record) = 8 /\
      (buy_account record < 256 ^ N.of_nat 2)%N /\
      (buy_order_capacity record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reserved_long_2 record) = 8 /\
      (sell_account record < 256 ^ N.of_nat 2)%N /\
      (sell_order_capacity record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (security_id_long record) ++
      encode_uint 1 (trade_capture_type record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_uint 8 (user_tag record) ++
      encode_bytes 8 (reserved_8 record) ++
      encode_uint 2 (buy_account record) ++
      encode_uint 1 (buy_order_capacity record) ++
      encode_bytes 8 (reserved_long_2 record) ++
      encode_uint 2 (sell_account record) ++
      encode_uint 1 (sell_order_capacity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (quantity_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (security_id_long_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (trade_capture_type_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (user_tag_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (reserved_8_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (buy_account_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (buy_order_capacity_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (reserved_long_2_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (sell_account_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (sell_order_capacity_value, bytes) =>
                                                      Some ({| quantity := quantity_value; price := price_value; security_id_long := security_id_long_value; trade_capture_type := trade_capture_type_value; reserved_1 := reserved_1_value; user_tag := user_tag_value; reserved_8 := reserved_8_value; buy_account := buy_account_value; buy_order_capacity := buy_order_capacity_value; reserved_long_2 := reserved_long_2_value; sell_account := sell_account_value; sell_order_capacity := sell_order_capacity_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCaptureMessage.

  Module TradeMessage.

    (** The Trade message is published when an order executes. The Trade message is also used to communicate indicative trade reports at lock time for Market at Close orders. Note that the price and tradeRef values will be zero for indicative trade reports published when MaC orders are matched at lock time. *)
    Record t := {
      order_ref : N;
      quantity : N;
      price : N;
      side : N;
      trade_ref : N;
      ccp_code : N;
      liq_indicator : N;
      security_id_short : N;
      trade_timestamp : N;
      user_tag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (trade_ref record < 256 ^ N.of_nat 4)%N /\
      (ccp_code record < 256 ^ N.of_nat 1)%N /\
      (liq_indicator record < 256 ^ N.of_nat 1)%N /\
      (security_id_short record < 256 ^ N.of_nat 2)%N /\
      (trade_timestamp record < 256 ^ N.of_nat 8)%N /\
      (user_tag record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (order_ref record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (trade_ref record) ++
      encode_uint 1 (ccp_code record) ++
      encode_uint 1 (liq_indicator record) ++
      encode_uint 2 (security_id_short record) ++
      encode_uint 8 (trade_timestamp record) ++
      encode_uint 8 (user_tag record).

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
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (ccp_code_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (liq_indicator_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (security_id_short_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_timestamp_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (user_tag_value, bytes) =>
                                              Some ({| order_ref := order_ref_value; quantity := quantity_value; price := price_value; side := side_value; trade_ref := trade_ref_value; ccp_code := ccp_code_value; liq_indicator := liq_indicator_value; security_id_short := security_id_short_value; trade_timestamp := trade_timestamp_value; user_tag := user_tag_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TradeMessage.

  Module TradeBustMessage.

    (** If a trade is invalidated, a Trade Bust message is sent to notify the trading Member. *)
    Record t := {
      order_ref : N;
      quantity : N;
      price : N;
      side : N;
      trade_ref : N;
      bust_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (trade_ref record < 256 ^ N.of_nat 4)%N /\
      (bust_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (order_ref record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (trade_ref record) ++
      encode_uint 8 (bust_timestamp record).

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
                          | Some (bust_timestamp_value, bytes) =>
                              Some ({| order_ref := order_ref_value; quantity := quantity_value; price := price_value; side := side_value; trade_ref := trade_ref_value; bust_timestamp := bust_timestamp_value |}, bytes)
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

End A2XEquitiesTradingProtocolV292.
