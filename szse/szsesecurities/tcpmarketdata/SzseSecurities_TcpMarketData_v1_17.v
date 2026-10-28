From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Shenzhen Stock Exchange Szse Tcp Market Data

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
  *)

Module SzseSecuritiesTcpMarketDataV117.

  Module MessageHeader.

    (** Szse Mdgw Message Header, defining the type and body length of a message, transmitted without encryption *)
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

    (** Logon message is the first message sent out to Market Data GateWay by Vendor Supplied System. Vendor Supplied System sets up a connection with Market Data GateWay through a logon message, and Market Data GateWay confirms the logon success through a logon message of its own, so both sides transmit this message type. *)
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

    (** When the connection request from Vendor Supplied System is not accepted, Market Data GateWay sends a logout message to refuse the logon request. Vendor Supplied System also sends a logout message voluntarily to disconnect, so both sides transmit this message type. *)
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

    (** Sent on a market data channel every 3 seconds, carrying the sequence number of the last market data message on the channel. *)
    Record t := {
      channel_no : N;
      appl_last_seq_num : N;
      end_of_channel : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_last_seq_num record < 256 ^ N.of_nat 8)%N /\
      (end_of_channel record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_last_seq_num record) ++
      encode_uint 2 (end_of_channel record).

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
                  Some ({| channel_no := channel_no_value; appl_last_seq_num := appl_last_seq_num_value; end_of_channel := end_of_channel_value |}, bytes)
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

  End ChannelHeartbeatMessage.

  Module RetransmittingMessage.

    (** Vendor Supplied System sends a re-transmission message to Market Data GateWay, which returns the re-transmission data needed followed by a re-transmission message indicating completion, or the failure reason if it fails. Market Data GateWay handles multiple requests in the order in which they arrive, so this message type is transmitted by both sides; ResendStatus and RejectText are only effective on the gateway reply. *)
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
      Datatypes.length (news_id record) = 8 /\
      (resend_status record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reject_text record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (resend_type record) ++
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_beg_seq_num record) ++
      encode_uint 8 (appl_end_seq_num record) ++
      encode_bytes 8 (news_id record) ++
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
                      match decode_bytes 8 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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

  End RetransmittingMessage.

  Module ClientUserInformationReportingMessage.

    (** Vendor Supplied System reports the number of client users connected to it at the current time to the Market Data GateWay front-end processor at regular intervals. Only the Vendor Supplied System of a vendor sends this message. *)
    Record t := {
      orig_time : N;
      version_code : list byte;
      user_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orig_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (version_code record) = 16 /\
      (user_num record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (orig_time record) ++
      encode_bytes 16 (version_code record) ++
      encode_uint 2 (user_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (orig_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (version_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (user_num_value, bytes) =>
                  Some ({| orig_time := orig_time_value; version_code := version_code_value; user_num := user_num_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClientUserInformationReportingMessage.

  Module BusinessRejectMessage.

    (** Rejects an application layer message that satisfies the session layer rules but does not satisfy the rules of the business layer. It reports on an incorrect re-transmitted message or client user information reporting message declared by the user. *)
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

  Module RealTimeMarketStatusMessage.

    (** Released every 3 seconds, carrying the trading session state of a market and, for stock connect, the daily quota balance. *)
    Record t := {
      orig_time : N;
      channel_no : N;
      market_id : list byte;
      market_segment_id : list byte;
      trading_session_id : list byte;
      trading_session_sub_id : list byte;
      trad_ses_status : N;
      trad_ses_start_time : N;
      trad_ses_end_time : N;
      thredhold_amount : N;
      pos_amt : N;
      amounts_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orig_time record < 256 ^ N.of_nat 8)%N /\
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (market_id record) = 8 /\
      Datatypes.length (market_segment_id record) = 8 /\
      Datatypes.length (trading_session_id record) = 4 /\
      Datatypes.length (trading_session_sub_id record) = 4 /\
      (trad_ses_status record < 256 ^ N.of_nat 2)%N /\
      (trad_ses_start_time record < 256 ^ N.of_nat 8)%N /\
      (trad_ses_end_time record < 256 ^ N.of_nat 8)%N /\
      (thredhold_amount record < 256 ^ N.of_nat 8)%N /\
      (pos_amt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (amounts_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (orig_time record) ++
      encode_uint 2 (channel_no record) ++
      encode_bytes 8 (market_id record) ++
      encode_bytes 8 (market_segment_id record) ++
      encode_bytes 4 (trading_session_id record) ++
      encode_bytes 4 (trading_session_sub_id record) ++
      encode_uint 2 (trad_ses_status record) ++
      encode_uint 8 (trad_ses_start_time record) ++
      encode_uint 8 (trad_ses_end_time record) ++
      encode_uint 8 (thredhold_amount record) ++
      encode_uint 8 (pos_amt record) ++
      encode_bytes 1 (amounts_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (orig_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (channel_no_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (market_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (trading_session_id_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (trading_session_sub_id_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (trad_ses_status_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trad_ses_start_time_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trad_ses_end_time_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (thredhold_amount_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (pos_amt_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (amounts_status_value, bytes) =>
                                                      Some ({| orig_time := orig_time_value; channel_no := channel_no_value; market_id := market_id_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trading_session_sub_id := trading_session_sub_id_value; trad_ses_status := trad_ses_status_value; trad_ses_start_time := trad_ses_start_time_value; trad_ses_end_time := trad_ses_end_time_value; thredhold_amount := thredhold_amount_value; pos_amt := pos_amt_value; amounts_status := amounts_status_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 69.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RealTimeMarketStatusMessage.

  Module StatisticIndicatorSnapshotMessage.

    (** Snapshot carrying market data category 910, statistic indicators. *)
    Record t := {
      orig_time : N;
      channel_no : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      trading_phase_code : list byte;
      prev_close_px : N;
      num_trades : N;
      total_volume_trade : N;
      total_value_trade : N;
      stock_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orig_time record < 256 ^ N.of_nat 8)%N /\
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      Datatypes.length (trading_phase_code record) = 8 /\
      (prev_close_px record < 256 ^ N.of_nat 8)%N /\
      (num_trades record < 256 ^ N.of_nat 8)%N /\
      (total_volume_trade record < 256 ^ N.of_nat 8)%N /\
      (total_value_trade record < 256 ^ N.of_nat 8)%N /\
      (stock_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (orig_time record) ++
      encode_uint 2 (channel_no record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_bytes 8 (trading_phase_code record) ++
      encode_uint 8 (prev_close_px record) ++
      encode_uint 8 (num_trades record) ++
      encode_uint 8 (total_volume_trade record) ++
      encode_uint 8 (total_value_trade record) ++
      encode_uint 4 (stock_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (orig_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (channel_no_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (md_stream_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (security_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (security_id_source_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (trading_phase_code_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (prev_close_px_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (num_trades_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (total_volume_trade_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (total_value_trade_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (stock_num_value, bytes) =>
                                                  Some ({| orig_time := orig_time_value; channel_no := channel_no_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; trading_phase_code := trading_phase_code_value; prev_close_px := prev_close_px_value; num_trades := num_trades_value; total_volume_trade := total_volume_trade_value; total_value_trade := total_value_trade_value; stock_num := stock_num_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StatisticIndicatorSnapshotMessage.

  Module OrderTickDataInCallAuctionMessage.

    (** Order tick carrying market data categories 011 for equities, funds and bonds in the call auction of the spot market, 021 pledge-style repo and 041 call auction in options. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      price : N;
      order_qty : N;
      side : list byte;
      transac_time : N;
      ord_type : list byte;
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
      (transac_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (order_qty record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (transac_time record) ++
      encode_bytes 1 (ord_type record).

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
                                      | Some (transac_time_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (ord_type_value, bytes) =>
                                              Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; price := price_value; order_qty := order_qty_value; side := side_value; transac_time := transac_time_value; ord_type := ord_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
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
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderTickDataInCallAuctionMessage.

  Module OrderTickDataOfNegotiableTradeMessage.

    (** Order tick carrying market data categories 051 indication of interest of negotiable trade and 052 quote of negotiable trade. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      price : N;
      order_qty : N;
      side : list byte;
      transac_time : N;
      confirm_id : list byte;
      contactor : list byte;
      contact_info : list byte;
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
      (transac_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (confirm_id record) = 8 /\
      Datatypes.length (contactor record) = 12 /\
      Datatypes.length (contact_info record) = 30.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (order_qty record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (transac_time record) ++
      encode_bytes 8 (confirm_id record) ++
      encode_bytes 12 (contactor record) ++
      encode_bytes 30 (contact_info record).

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
                                      | Some (transac_time_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (confirm_id_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (contactor_value, bytes) =>
                                                  match decode_bytes 30 bytes with
                                                  | None => None
                                                  | Some (contact_info_value, bytes) =>
                                                      Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; price := price_value; order_qty := order_qty_value; side := side_value; transac_time := transac_time_value; confirm_id := confirm_id_value; contactor := contactor_value; contact_info := contact_info_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 100.
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

  End OrderTickDataOfNegotiableTradeMessage.

  Module OrderTickDataOfSecurityLendingMessage.

    (** Order tick carrying market data category 071, security lending. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      price : N;
      order_qty : N;
      side : list byte;
      transac_time : N;
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
      (transac_time record < 256 ^ N.of_nat 8)%N /\
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
      encode_uint 8 (transac_time record) ++
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
                                      | Some (transac_time_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (expiration_days_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (expiration_type_value, bytes) =>
                                                  Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; price := price_value; order_qty := order_qty_value; side := side_value; transac_time := transac_time_value; expiration_days := expiration_days_value; expiration_type := expiration_type_value |}, bytes)
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

  End OrderTickDataOfSecurityLendingMessage.

  Module OrderTickDataOfSpotBondTradingMatchingDealMessage.

    (** Order tick carrying market data categories 021 bond general pledged repo matching deal and 411 spot bond trading matching deal. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      price : N;
      order_qty : N;
      side : list byte;
      transac_time : N;
      ord_type : list byte;
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
      (transac_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (order_qty record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (transac_time record) ++
      encode_bytes 1 (ord_type record).

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
                                      | Some (transac_time_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (ord_type_value, bytes) =>
                                              Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; price := price_value; order_qty := order_qty_value; side := side_value; transac_time := transac_time_value; ord_type := ord_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
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
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderTickDataOfSpotBondTradingMatchingDealMessage.

  Module OrderTickDataOfSpotBondTradingQuotationMessage.

    (** Order tick carrying market data categories 415 spot bond trading declaration of intent and 417 spot bond trading large amount matching deal, for spot bond trading other than bid. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      price : N;
      order_qty : N;
      side : list byte;
      transac_time : N;
      quote_id : list byte;
      member_id : list byte;
      investor_type : list byte;
      investor_id : list byte;
      investor_name : list byte;
      trader_code : list byte;
      settl_period : N;
      settl_type : N;
      memo : list byte;
      min_qty : N;
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
      (transac_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_id record) = 10 /\
      Datatypes.length (member_id record) = 6 /\
      Datatypes.length (investor_type record) = 2 /\
      Datatypes.length (investor_id record) = 10 /\
      Datatypes.length (investor_name record) = 120 /\
      Datatypes.length (trader_code record) = 8 /\
      (settl_period record < 256 ^ N.of_nat 1)%N /\
      (settl_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (memo record) = 160 /\
      (min_qty record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (order_qty record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (transac_time record) ++
      encode_bytes 10 (quote_id record) ++
      encode_bytes 6 (member_id record) ++
      encode_bytes 2 (investor_type record) ++
      encode_bytes 10 (investor_id record) ++
      encode_bytes 120 (investor_name record) ++
      encode_bytes 8 (trader_code record) ++
      encode_uint 1 (settl_period record) ++
      encode_uint 2 (settl_type record) ++
      encode_bytes 160 (memo record) ++
      encode_uint 8 (min_qty record).

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
                                      | Some (transac_time_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (quote_id_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (member_id_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (investor_type_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (investor_id_value, bytes) =>
                                                          match decode_bytes 120 bytes with
                                                          | None => None
                                                          | Some (investor_name_value, bytes) =>
                                                              match decode_bytes 8 bytes with
                                                              | None => None
                                                              | Some (trader_code_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (settl_period_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (settl_type_value, bytes) =>
                                                                          match decode_bytes 160 bytes with
                                                                          | None => None
                                                                          | Some (memo_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (min_qty_value, bytes) =>
                                                                                  Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; price := price_value; order_qty := order_qty_value; side := side_value; transac_time := transac_time_value; quote_id := quote_id_value; member_id := member_id_value; investor_type := investor_type_value; investor_id := investor_id_value; investor_name := investor_name_value; trader_code := trader_code_value; settl_period := settl_period_value; settl_type := settl_type_value; memo := memo_value; min_qty := min_qty_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 377.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderTickDataOfSpotBondTradingQuotationMessage.

  Module OrderTickDataOfBidQuotationMessage.

    (** Order tick carrying market data category 416, spot bond trading bidding deal, covering the bid order and bid reservation. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      security_id : list byte;
      security_id_source : list byte;
      price : N;
      order_qty : N;
      side : list byte;
      transac_time : N;
      member_id : list byte;
      investor_type : list byte;
      investor_id : list byte;
      investor_name : list byte;
      trader_code : list byte;
      settl_period : N;
      settl_type : N;
      memo : list byte;
      secondary_order_id : list byte;
      bid_trans_type : N;
      bid_exec_inst_type : N;
      low_limit_price : N;
      high_limit_price : N;
      min_qty : N;
      trade_date : N;
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
      (transac_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (member_id record) = 6 /\
      Datatypes.length (investor_type record) = 2 /\
      Datatypes.length (investor_id record) = 10 /\
      Datatypes.length (investor_name record) = 120 /\
      Datatypes.length (trader_code record) = 8 /\
      (settl_period record < 256 ^ N.of_nat 1)%N /\
      (settl_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (memo record) = 160 /\
      Datatypes.length (secondary_order_id record) = 16 /\
      (bid_trans_type record < 256 ^ N.of_nat 2)%N /\
      (bid_exec_inst_type record < 256 ^ N.of_nat 2)%N /\
      (low_limit_price record < 256 ^ N.of_nat 8)%N /\
      (high_limit_price record < 256 ^ N.of_nat 8)%N /\
      (min_qty record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (order_qty record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (transac_time record) ++
      encode_bytes 6 (member_id record) ++
      encode_bytes 2 (investor_type record) ++
      encode_bytes 10 (investor_id record) ++
      encode_bytes 120 (investor_name record) ++
      encode_bytes 8 (trader_code record) ++
      encode_uint 1 (settl_period record) ++
      encode_uint 2 (settl_type record) ++
      encode_bytes 160 (memo record) ++
      encode_bytes 16 (secondary_order_id record) ++
      encode_uint 2 (bid_trans_type record) ++
      encode_uint 2 (bid_exec_inst_type record) ++
      encode_uint 8 (low_limit_price record) ++
      encode_uint 8 (high_limit_price record) ++
      encode_uint 8 (min_qty record) ++
      encode_uint 4 (trade_date record).

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
                                      | Some (transac_time_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (member_id_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (investor_type_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (investor_id_value, bytes) =>
                                                      match decode_bytes 120 bytes with
                                                      | None => None
                                                      | Some (investor_name_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (trader_code_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (settl_period_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (settl_type_value, bytes) =>
                                                                      match decode_bytes 160 bytes with
                                                                      | None => None
                                                                      | Some (memo_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (secondary_order_id_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (bid_trans_type_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_exec_inst_type_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (low_limit_price_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (high_limit_price_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (min_qty_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trade_date_value, bytes) =>
                                                                                                      Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; security_id := security_id_value; security_id_source := security_id_source_value; price := price_value; order_qty := order_qty_value; side := side_value; transac_time := transac_time_value; member_id := member_id_value; investor_type := investor_type_value; investor_id := investor_id_value; investor_name := investor_name_value; trader_code := trader_code_value; settl_period := settl_period_value; settl_type := settl_type_value; memo := memo_value; secondary_order_id := secondary_order_id_value; bid_trans_type := bid_trans_type_value; bid_exec_inst_type := bid_exec_inst_type_value; low_limit_price := low_limit_price_value; high_limit_price := high_limit_price_value; min_qty := min_qty_value; trade_date := trade_date_value |}, bytes)
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
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 407.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 bound_23]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderTickDataOfBidQuotationMessage.

  Module TransactionTickDataInCallAuctionMessage.

    (** Transaction tick carrying market data categories 011 for equities, funds and bonds in the call auction of the spot market, 021 pledge-style repo and 041 call auction in options. The sequence number of tick order and tick transaction data in the same channel is consecutive. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      bid_appl_seq_num : N;
      offer_appl_seq_num : N;
      security_id : list byte;
      security_id_source : list byte;
      last_px : N;
      last_qty : N;
      exec_type : list byte;
      transac_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      (bid_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (offer_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_type record) = 1 /\
      (transac_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_uint 8 (bid_appl_seq_num record) ++
      encode_uint 8 (offer_appl_seq_num record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 8 (transac_time record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_appl_seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (offer_appl_seq_num_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (exec_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (transac_time_value, bytes) =>
                                                  Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; bid_appl_seq_num := bid_appl_seq_num_value; offer_appl_seq_num := offer_appl_seq_num_value; security_id := security_id_value; security_id_source := security_id_source_value; last_px := last_px_value; last_qty := last_qty_value; exec_type := exec_type_value; transac_time := transac_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TransactionTickDataInCallAuctionMessage.

  Module TransactionTickDataOfNegotiableTradeMessage.

    (** Transaction tick carrying market data categories 051 indication of interest of negotiable trade and 052 quote of negotiable trade. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      bid_appl_seq_num : N;
      offer_appl_seq_num : N;
      security_id : list byte;
      security_id_source : list byte;
      last_px : N;
      last_qty : N;
      exec_type : list byte;
      transac_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      (bid_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (offer_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_type record) = 1 /\
      (transac_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_uint 8 (bid_appl_seq_num record) ++
      encode_uint 8 (offer_appl_seq_num record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 8 (transac_time record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_appl_seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (offer_appl_seq_num_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (exec_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (transac_time_value, bytes) =>
                                                  Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; bid_appl_seq_num := bid_appl_seq_num_value; offer_appl_seq_num := offer_appl_seq_num_value; security_id := security_id_value; security_id_source := security_id_source_value; last_px := last_px_value; last_qty := last_qty_value; exec_type := exec_type_value; transac_time := transac_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TransactionTickDataOfNegotiableTradeMessage.

  Module TransactionTickDataOfSecurityLendingMessage.

    (** Transaction tick carrying market data category 071, security lending. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      bid_appl_seq_num : N;
      offer_appl_seq_num : N;
      security_id : list byte;
      security_id_source : list byte;
      last_px : N;
      last_qty : N;
      exec_type : list byte;
      transac_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      (bid_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (offer_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_type record) = 1 /\
      (transac_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_uint 8 (bid_appl_seq_num record) ++
      encode_uint 8 (offer_appl_seq_num record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 8 (transac_time record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_appl_seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (offer_appl_seq_num_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (exec_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (transac_time_value, bytes) =>
                                                  Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; bid_appl_seq_num := bid_appl_seq_num_value; offer_appl_seq_num := offer_appl_seq_num_value; security_id := security_id_value; security_id_source := security_id_source_value; last_px := last_px_value; last_qty := last_qty_value; exec_type := exec_type_value; transac_time := transac_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TransactionTickDataOfSecurityLendingMessage.

  Module TransactionTickDataOfBondGeneralPledgedRepoMessage.

    (** Transaction tick carrying market data categories 021 bond general pledged repo matching deal and 411 spot bond trading matching deal. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      bid_appl_seq_num : N;
      offer_appl_seq_num : N;
      security_id : list byte;
      security_id_source : list byte;
      last_px : N;
      last_qty : N;
      exec_type : list byte;
      transac_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      (bid_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (offer_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_type record) = 1 /\
      (transac_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_uint 8 (bid_appl_seq_num record) ++
      encode_uint 8 (offer_appl_seq_num record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 8 (transac_time record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_appl_seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (offer_appl_seq_num_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (exec_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (transac_time_value, bytes) =>
                                                  Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; bid_appl_seq_num := bid_appl_seq_num_value; offer_appl_seq_num := offer_appl_seq_num_value; security_id := security_id_value; security_id_source := security_id_source_value; last_px := last_px_value; last_qty := last_qty_value; exec_type := exec_type_value; transac_time := transac_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TransactionTickDataOfBondGeneralPledgedRepoMessage.

  Module TransactionTickDataOfSpotBondTradingQuotationMessage.

    (** Transaction tick carrying market data categories 412 spot bond trading negotiated deal, 413 click deal, 414 inquiry deal and 417 large amount matching deal, for spot bond trading other than bid. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      bid_appl_seq_num : N;
      offer_appl_seq_num : N;
      security_id : list byte;
      security_id_source : list byte;
      last_px : N;
      last_qty : N;
      exec_type : list byte;
      transac_time : N;
      settl_period : N;
      settl_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      (bid_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (offer_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_type record) = 1 /\
      (transac_time record < 256 ^ N.of_nat 8)%N /\
      (settl_period record < 256 ^ N.of_nat 1)%N /\
      (settl_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_uint 8 (bid_appl_seq_num record) ++
      encode_uint 8 (offer_appl_seq_num record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 8 (transac_time record) ++
      encode_uint 1 (settl_period record) ++
      encode_uint 2 (settl_type record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_appl_seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (offer_appl_seq_num_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (exec_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (transac_time_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (settl_period_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (settl_type_value, bytes) =>
                                                          Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; bid_appl_seq_num := bid_appl_seq_num_value; offer_appl_seq_num := offer_appl_seq_num_value; security_id := security_id_value; security_id_source := security_id_source_value; last_px := last_px_value; last_qty := last_qty_value; exec_type := exec_type_value; transac_time := transac_time_value; settl_period := settl_period_value; settl_type := settl_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 69.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TransactionTickDataOfSpotBondTradingQuotationMessage.

  Module TransactionTickDataOfBidQuotationMessage.

    (** Transaction tick carrying market data category 416, spot bond trading bidding deal. *)
    Record t := {
      channel_no : N;
      appl_seq_num : N;
      md_stream_id : list byte;
      bid_appl_seq_num : N;
      offer_appl_seq_num : N;
      security_id : list byte;
      security_id_source : list byte;
      last_px : N;
      last_qty : N;
      exec_type : list byte;
      transac_time : N;
      settl_period : N;
      settl_type : N;
      secondary_order_id : list byte;
      bid_exec_inst_type : N;
      margin_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_no record < 256 ^ N.of_nat 2)%N /\
      (appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (md_stream_id record) = 3 /\
      (bid_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      (offer_appl_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_type record) = 1 /\
      (transac_time record < 256 ^ N.of_nat 8)%N /\
      (settl_period record < 256 ^ N.of_nat 1)%N /\
      (settl_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (secondary_order_id record) = 16 /\
      (bid_exec_inst_type record < 256 ^ N.of_nat 2)%N /\
      (margin_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_no record) ++
      encode_uint 8 (appl_seq_num record) ++
      encode_bytes 3 (md_stream_id record) ++
      encode_uint 8 (bid_appl_seq_num record) ++
      encode_uint 8 (offer_appl_seq_num record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 8 (transac_time record) ++
      encode_uint 1 (settl_period record) ++
      encode_uint 2 (settl_type record) ++
      encode_bytes 16 (secondary_order_id record) ++
      encode_uint 2 (bid_exec_inst_type record) ++
      encode_uint 8 (margin_price record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_appl_seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (offer_appl_seq_num_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (exec_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (transac_time_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (settl_period_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (settl_type_value, bytes) =>
                                                          match decode_bytes 16 bytes with
                                                          | None => None
                                                          | Some (secondary_order_id_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (bid_exec_inst_type_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (margin_price_value, bytes) =>
                                                                      Some ({| channel_no := channel_no_value; appl_seq_num := appl_seq_num_value; md_stream_id := md_stream_id_value; bid_appl_seq_num := bid_appl_seq_num_value; offer_appl_seq_num := offer_appl_seq_num_value; security_id := security_id_value; security_id_source := security_id_source_value; last_px := last_px_value; last_qty := last_qty_value; exec_type := exec_type_value; transac_time := transac_time_value; settl_period := settl_period_value; settl_type := settl_type_value; secondary_order_id := secondary_order_id_value; bid_exec_inst_type := bid_exec_inst_type_value; margin_price := margin_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 95.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TransactionTickDataOfBidQuotationMessage.

  Module MessageTail.

    (** Szse Mdgw Message Tail, defining the checksum of a message, transmitted without encryption *)
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

End SzseSecuritiesTcpMarketDataV117.
