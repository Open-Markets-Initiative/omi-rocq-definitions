From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Beijing Stock Exchange Bjse Tcp Market Data

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
      - the dispatch that chooses a message by its type
      - a run counted by a field
      - a length prefix framing what follows

    License: MIT No Attribution
  *)

Module BjseSecuritiesTcpMarketDataV11.

  Module MessageHeader.

    (** Bjse Bjqg Message Header, defining the type and body length of a message, transmitted without encryption *)
    Record t := {
      msg_type : N;
      body_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_type record < 256 ^ N.of_nat 4)%N /\
      (body_length record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (msg_type record) ++
      encode_uint 4 (body_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (msg_type_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (body_length_value, bytes) =>
              Some ({| msg_type := msg_type_value; body_length := body_length_value |}, bytes)
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

  End MessageHeader.

  Module LogonMessage.

    (** The first message the Vendor Supplied System sends to the market quotation gateway, which confirms a successful logon with a Logon of its own, so both sides transmit this message type. *)
    Record t := {
      sender_comp_id : list byte;
      target_comp_id : list byte;
      heart_bt_int : N;
      password : list byte;
      default_appl_ver_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sender_comp_id record) = 20 /\
      Datatypes.length (target_comp_id record) = 20 /\
      (heart_bt_int record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (password record) = 16 /\
      Datatypes.length (default_appl_ver_id record) = 32.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (sender_comp_id record) ++
      encode_bytes 20 (target_comp_id record) ++
      encode_uint 4 (heart_bt_int record) ++
      encode_bytes 16 (password record) ++
      encode_bytes 32 (default_appl_ver_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (sender_comp_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (target_comp_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (heart_bt_int_value, bytes) =>
                  match decode_bytes 16 bytes with
                  | None => None
                  | Some (password_value, bytes) =>
                      match decode_bytes 32 bytes with
                      | None => None
                      | Some (default_appl_ver_id_value, bytes) =>
                          Some ({| sender_comp_id := sender_comp_id_value; target_comp_id := target_comp_id_value; heart_bt_int := heart_bt_int_value; password := password_value; default_appl_ver_id := default_appl_ver_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 92.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonMessage.

  Module LogoutMessage.

    (** Sent by the gateway to refuse a logon request it does not accept; the Vendor Supplied System may also send it to end the connection, so both sides transmit this message type. *)
    Record t := {
      session_status : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_status record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (text record) = 200.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_status record) ++
      encode_bytes 200 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_status_value, bytes) =>
          match decode_bytes 200 bytes with
          | None => None
          | Some (text_value, bytes) =>
              Some ({| session_status := session_status_value; text := text_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 204.
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

  Module ChannelHeartbeatMessage.

    (** Sent on a market data channel every 3 seconds, carrying the sequence number of the last tick message on the channel. *)
    Record t := {
      channel_no : N;
      appl_last_seq_num : N;
      end_of_channel : N;
      orig_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_last_seq_num record < 256 ^ N.of_nat 8)%N /\
      (end_of_channel record < 256 ^ N.of_nat 2)%N /\
      (orig_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_last_seq_num record) ++
      encode_uint 2 (end_of_channel record) ++
      encode_uint 8 (orig_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_last_seq_num_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (end_of_channel_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (orig_time_value, bytes) =>
                      Some ({| channel_no := channel_no_value; appl_last_seq_num := appl_last_seq_num_value; end_of_channel := end_of_channel_value; orig_time := orig_time_value |}, bytes)
                  end
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

  End ChannelHeartbeatMessage.

  Module RetransmissionMessage.

    (** Sent by the Vendor Supplied System to request tick data or announcements again; the gateway returns the data and then the same message type to mark the retransmission complete or report why it failed, so both sides transmit this message type. *)
    Record t := {
      resend_type : N;
      channel_no : N;
      appl_beg_seq_num : N;
      appl_end_seq_num : N;
      news_id : list byte;
      resend_status : N;
      reject_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (resend_type record < 256 ^ N.of_nat 1)%N /\
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_beg_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_end_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (news_id record) = 16 /\
      (resend_status record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reject_text record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (resend_type record) ++
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_beg_seq_num record) ++
      encode_uint 8 (appl_end_seq_num record) ++
      encode_bytes 16 (news_id record) ++
      encode_uint 1 (resend_status record) ++
      encode_bytes 16 (reject_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (resend_type_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (channel_no_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (appl_beg_seq_num_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (appl_end_seq_num_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (news_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (resend_status_value, bytes) =>
                              match decode_bytes 16 bytes with
                              | None => None
                              | Some (reject_text_value, bytes) =>
                                  Some ({| resend_type := resend_type_value; channel_no := channel_no_value; appl_beg_seq_num := appl_beg_seq_num_value; appl_end_seq_num := appl_end_seq_num_value; news_id := news_id_value; resend_status := resend_status_value; reject_text := reject_text_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
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
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RetransmissionMessage.

  Module BusinessRejectMessage.

    (** Rejects an application message that satisfies the session layer rules but not the business layer rules, mainly an invalid retransmission request. *)
    Record t := {
      ref_seq_num : N;
      ref_msg_type : N;
      business_reject_ref_id : list byte;
      business_reject_reason : N;
      business_reject_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (ref_seq_num record < 256 ^ N.of_nat 8)%N /\
      (ref_msg_type record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (business_reject_ref_id record) = 10 /\
      (business_reject_reason record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (business_reject_text record) = 50.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (ref_seq_num record) ++
      encode_uint 4 (ref_msg_type record) ++
      encode_bytes 10 (business_reject_ref_id record) ++
      encode_uint 2 (business_reject_reason record) ++
      encode_bytes 50 (business_reject_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (ref_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (ref_msg_type_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (business_reject_ref_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (business_reject_reason_value, bytes) =>
                      match decode_bytes 50 bytes with
                      | None => None
                      | Some (business_reject_text_value, bytes) =>
                          Some ({| ref_seq_num := ref_seq_num_value; ref_msg_type := ref_msg_type_value; business_reject_ref_id := business_reject_ref_id_value; business_reject_reason := business_reject_reason_value; business_reject_text := business_reject_text_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BusinessRejectMessage.

  Module BondSpotMatchingLargeOrderTickMessage.

    (** Order tick of large lot matching in spot bond trading, market data category 011, published in real time. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      price : N;
      order_qty : N;
      side : list byte;
      transact_time : N;
      ord_type : list byte;
      settl_type : list byte;
      settl_period : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1 /\
      Datatypes.length (settl_type record) = 1 /\
      Datatypes.length (settl_period record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (order_qty record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 1 (ord_type record) ++
      encode_bytes 1 (settl_type record) ++
      encode_bytes 1 (settl_period record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (md_stream_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (security_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (security_id_source_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (order_qty_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (transact_time_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (ord_type_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (settl_type_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (settl_period_value, bytes) =>
                                                      Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; price := price_value; order_qty := order_qty_value; side := side_value; transact_time := transact_time_value; ord_type := ord_type_value; settl_type := settl_type_value; settl_period := settl_period_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 53.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondSpotMatchingLargeOrderTickMessage.

  Module AgreementTradingOrderTickMessage.

    (** Order tick of agreement trading on the trading support platform, market data category 021, published in real time; not yet enabled. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      price : N;
      order_qty : N;
      side : list byte;
      transact_time : N;
      confirm_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (order_qty record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (confirm_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (md_stream_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (security_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (security_id_source_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (order_qty_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (transact_time_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (confirm_id_value, bytes) =>
                                              Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; price := price_value; order_qty := order_qty_value; side := side_value; transact_time := transact_time_value; confirm_id := confirm_id_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AgreementTradingOrderTickMessage.

  Module SecuritiesLendingOrderTickMessage.

    (** Order tick of refinancing securities lending, market data category 023, published in real time; not yet enabled. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      price : N;
      order_qty : N;
      side : list byte;
      transact_time : N;
      expiration_days : N;
      expiration_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (expiration_days record < 256 ^ N.of_nat 2)%N /\
      (expiration_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (order_qty record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 2 (expiration_days record) ++
      encode_uint 1 (expiration_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (md_stream_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (security_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (security_id_source_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (order_qty_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (transact_time_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (expiration_days_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (expiration_type_value, bytes) =>
                                                  Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; price := price_value; order_qty := order_qty_value; side := side_value; transact_time := transact_time_value; expiration_days := expiration_days_value; expiration_type := expiration_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 53.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesLendingOrderTickMessage.

  Module BondSpotMatchingLargeTradeTickMessage.

    (** Trade tick of large lot matching in spot bond trading, market data category 011, published in real time. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      bid_appl_seq_num : N;
      ask_appl_seq_num : N;
      trade_price : N;
      trade_qty : N;
      trade_money : N;
      exec_type : list byte;
      transact_time : N;
      settl_period : list byte;
      settl_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (bid_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (ask_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_qty record < 256 ^ N.of_nat 8)%N /\
      (trade_money record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_type record) = 1 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (settl_period record) = 1 /\
      Datatypes.length (settl_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (bid_appl_seq_num record) ++
      encode_uint 8 (ask_appl_seq_num record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (trade_qty record) ++
      encode_uint 8 (trade_money record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 1 (settl_period record) ++
      encode_bytes 1 (settl_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (md_stream_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (security_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (security_id_source_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (bid_appl_seq_num_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (ask_appl_seq_num_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trade_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (trade_money_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (exec_type_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (transact_time_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (settl_period_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (settl_type_value, bytes) =>
                                                              Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; bid_appl_seq_num := bid_appl_seq_num_value; ask_appl_seq_num := ask_appl_seq_num_value; trade_price := trade_price_value; trade_qty := trade_qty_value; trade_money := trade_money_value; exec_type := exec_type_value; transact_time := transact_time_value; settl_period := settl_period_value; settl_type := settl_type_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondSpotMatchingLargeTradeTickMessage.

  Module BondSpotNegotiatedTradeTickMessage.

    (** Trade tick of negotiated trading in spot bond trading, market data category 012, published in real time. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      bid_appl_seq_num : N;
      ask_appl_seq_num : N;
      trade_price : N;
      trade_qty : N;
      trade_money : N;
      exec_type : list byte;
      transact_time : N;
      settl_period : list byte;
      settl_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (bid_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (ask_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_qty record < 256 ^ N.of_nat 8)%N /\
      (trade_money record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_type record) = 1 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (settl_period record) = 1 /\
      Datatypes.length (settl_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (bid_appl_seq_num record) ++
      encode_uint 8 (ask_appl_seq_num record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (trade_qty record) ++
      encode_uint 8 (trade_money record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 1 (settl_period record) ++
      encode_bytes 1 (settl_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (md_stream_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (security_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (security_id_source_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (bid_appl_seq_num_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (ask_appl_seq_num_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trade_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (trade_money_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (exec_type_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (transact_time_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (settl_period_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (settl_type_value, bytes) =>
                                                              Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; bid_appl_seq_num := bid_appl_seq_num_value; ask_appl_seq_num := ask_appl_seq_num_value; trade_price := trade_price_value; trade_qty := trade_qty_value; trade_money := trade_money_value; exec_type := exec_type_value; transact_time := transact_time_value; settl_period := settl_period_value; settl_type := settl_type_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondSpotNegotiatedTradeTickMessage.

  Module SecuritiesLendingTradeTickMessage.

    (** Trade tick of refinancing securities lending, market data category 023, published in real time; it has no extension fields and is not yet enabled. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      bid_appl_seq_num : N;
      ask_appl_seq_num : N;
      trade_price : N;
      trade_qty : N;
      trade_money : N;
      exec_type : list byte;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (bid_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (ask_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_qty record < 256 ^ N.of_nat 8)%N /\
      (trade_money record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_type record) = 1 /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (bid_appl_seq_num record) ++
      encode_uint 8 (ask_appl_seq_num record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (trade_qty record) ++
      encode_uint 8 (trade_money record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (appl_seq_num_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (md_stream_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (security_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (security_id_source_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (bid_appl_seq_num_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (ask_appl_seq_num_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trade_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (trade_money_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (exec_type_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (transact_time_value, bytes) =>
                                                      Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; bid_appl_seq_num := bid_appl_seq_num_value; ask_appl_seq_num := ask_appl_seq_num_value; trade_price := trade_price_value; trade_qty := trade_qty_value; trade_money := trade_money_value; exec_type := exec_type_value; transact_time := transact_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesLendingTradeTickMessage.

  Module MessageTail.

    (** Bjse Bjqg Message Tail, defining the checksum of a message, transmitted without encryption *)
    Record t := {
      checksum : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (checksum record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (checksum record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (checksum_value, bytes) =>
          Some ({| checksum := checksum_value |}, bytes)
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

  End MessageTail.

End BjseSecuritiesTcpMarketDataV11.
