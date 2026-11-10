From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Equities Exchange and Quotations Neeq Order Entry

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

    License: MIT No Attribution
  *)

Module NeeqSecuritiesOrderEntryV11.

  Module MessageHeader.

    (** Bjse Bjtg Message Header, defining the type and body length of a message, transmitted without encryption *)
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

    (** The first message the order management system sends to the trading gateway, which confirms a successful logon with a Logon of its own, so both sides transmit this message type. *)
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

    (** Sent by the trading gateway to refuse a logon, and by either side to end the session; the receiver answers with a Logout of its own, so both sides transmit this message type. *)
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

  Module BusinessRejectMessage.

    (** Sent by the trading gateway when a submission fails a basic validity check, such as an unknown security code or a submission outside its time window. *)
    Record t := {
      appl_id : list byte;
      transact_time : N;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      ref_seq_num : N;
      ref_msg_type : N;
      business_reject_ref_id : list byte;
      business_reject_reason : N;
      business_reject_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (ref_seq_num record < 256 ^ N.of_nat 8)%N /\
      (ref_msg_type record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (business_reject_ref_id record) = 10 /\
      (business_reject_reason record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (business_reject_text record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 8 (ref_seq_num record) ++
      encode_uint 4 (ref_msg_type record) ++
      encode_bytes 10 (business_reject_ref_id record) ++
      encode_uint 2 (business_reject_reason record) ++
      encode_bytes 50 (business_reject_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transact_time_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (submitting_pbuid_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (security_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (security_id_source_value, bytes) =>
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
                                              Some ({| appl_id := appl_id_value; transact_time := transact_time_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; ref_seq_num := ref_seq_num_value; ref_msg_type := ref_msg_type_value; business_reject_ref_id := business_reject_ref_id_value; business_reject_reason := business_reject_reason_value; business_reject_text := business_reject_text_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 103.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
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

  End BusinessRejectMessage.

  Module PlatformStateInfoMessage.

    (** Sent by the trading gateway after logon and whenever a platform changes state, so the order management system can control when it submits orders. *)
    Record t := {
      platform_id : N;
      platform_state : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (platform_id record < 256 ^ N.of_nat 2)%N /\
      (platform_state record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (platform_id record) ++
      encode_uint 2 (platform_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (platform_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (platform_state_value, bytes) =>
              Some ({| platform_id := platform_id_value; platform_state := platform_state_value |}, bytes)
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

  End PlatformStateInfoMessage.

  Module ReportFinishedMessage.

    (** Sent by the trading gateway when every report of the trading day for a platform partition has been sent; its record number continues the numbering of the partition's reports. *)
    Record t := {
      partition_no : N;
      report_index : N;
      platform_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      (platform_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_uint 2 (platform_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (platform_id_value, bytes) =>
                  Some ({| partition_no := partition_no_value; report_index := report_index_value; platform_id := platform_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End ReportFinishedMessage.

  Module TradingSessionStatusMessage.

    (** Sent by the trading gateway after logon and whenever the trading session of the connected platform changes; only the fixed income platform currently sends it. *)
    Record t := {
      market_id : list byte;
      market_segment_id : list byte;
      trading_session_id : list byte;
      trading_session_sub_id : list byte;
      trad_ses_status : N;
      trad_ses_start_time : N;
      trad_ses_end_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_id record) = 8 /\
      Datatypes.length (market_segment_id record) = 8 /\
      Datatypes.length (trading_session_id record) = 4 /\
      Datatypes.length (trading_session_sub_id record) = 4 /\
      (trad_ses_status record < 256 ^ N.of_nat 2)%N /\
      (trad_ses_start_time record < 256 ^ N.of_nat 8)%N /\
      (trad_ses_end_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (market_id record) ++
      encode_bytes 8 (market_segment_id record) ++
      encode_bytes 4 (trading_session_id record) ++
      encode_bytes 4 (trading_session_sub_id record) ++
      encode_uint 2 (trad_ses_status record) ++
      encode_uint 8 (trad_ses_start_time record) ++
      encode_uint 8 (trad_ses_end_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                                  Some ({| market_id := market_id_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trading_session_sub_id := trading_session_sub_id_value; trad_ses_status := trad_ses_status_value; trad_ses_start_time := trad_ses_start_time_value; trad_ses_end_time := trad_ses_end_time_value |}, bytes)
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

  End TradingSessionStatusMessage.

  Module BondSpotMatchingNewOrderMessage.

    (** New order for spot bond trading by matching, ApplID 010. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      cl_ord_id : list byte;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
      stop_px : N;
      min_qty : N;
      max_price_levels : N;
      time_in_force : list byte;
      cash_margin : list byte;
      settl_type : list byte;
      settl_period : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (min_qty record < 256 ^ N.of_nat 8)%N /\
      (max_price_levels record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (time_in_force record) = 1 /\
      Datatypes.length (cash_margin record) = 1 /\
      Datatypes.length (settl_type record) = 1 /\
      Datatypes.length (settl_period record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 8 (min_qty record) ++
      encode_uint 2 (max_price_levels record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_bytes 1 (cash_margin record) ++
      encode_bytes 1 (settl_type record) ++
      encode_bytes 1 (settl_period record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (cl_ord_id_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (account_id_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (branch_id_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (order_restrictions_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (ord_type_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (order_qty_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (stop_px_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (min_qty_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (max_price_levels_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (time_in_force_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (cash_margin_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (settl_type_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (settl_period_value, bytes) =>
                                                                                                  Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; cl_ord_id := cl_ord_id_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value; stop_px := stop_px_value; min_qty := min_qty_value; max_price_levels := max_price_levels_value; time_in_force := time_in_force_value; cash_margin := cash_margin_value; settl_type := settl_type_value; settl_period := settl_period_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 131.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondSpotMatchingNewOrderMessage.

  Module CentralizedAuctionNewOrderMessage.

    (** New order for centralized auction stock trading, ApplID 040. Not yet enabled. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      cl_ord_id : list byte;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
      stop_px : N;
      min_qty : N;
      max_price_levels : N;
      time_in_force : list byte;
      cash_margin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (min_qty record < 256 ^ N.of_nat 8)%N /\
      (max_price_levels record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (time_in_force record) = 1 /\
      Datatypes.length (cash_margin record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 8 (min_qty record) ++
      encode_uint 2 (max_price_levels record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_bytes 1 (cash_margin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (cl_ord_id_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (account_id_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (branch_id_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (order_restrictions_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (ord_type_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (order_qty_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (stop_px_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (min_qty_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (max_price_levels_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (time_in_force_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (cash_margin_value, bytes) =>
                                                                                          Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; cl_ord_id := cl_ord_id_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value; stop_px := stop_px_value; min_qty := min_qty_value; max_price_levels := max_price_levels_value; time_in_force := time_in_force_value; cash_margin := cash_margin_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 129.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CentralizedAuctionNewOrderMessage.

  Module ConversionNewOrderMessage.

    (** New order for conversion, ApplID 041. Not yet enabled. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      cl_ord_id : list byte;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (cl_ord_id_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (account_id_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (branch_id_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (order_restrictions_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (ord_type_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (order_qty_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; cl_ord_id := cl_ord_id_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConversionNewOrderMessage.

  Module InquiryNewOrderMessage.

    (** New order for inquiry, ApplID 042. Not yet enabled. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      cl_ord_id : list byte;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (cl_ord_id_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (account_id_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (branch_id_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (order_restrictions_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (ord_type_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (order_qty_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; cl_ord_id := cl_ord_id_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InquiryNewOrderMessage.

  Module SubscriptionNewOrderMessage.

    (** New order for subscription, ApplID 043. Not yet enabled. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      cl_ord_id : list byte;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (cl_ord_id_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (account_id_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (branch_id_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (order_restrictions_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (ord_type_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (order_qty_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; cl_ord_id := cl_ord_id_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SubscriptionNewOrderMessage.

  Module PutBackNewOrderMessage.

    (** New order for put back, ApplID 044. Not yet enabled. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      cl_ord_id : list byte;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (cl_ord_id_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (account_id_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (branch_id_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (order_restrictions_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (ord_type_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (order_qty_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; cl_ord_id := cl_ord_id_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PutBackNewOrderMessage.

  Module TenderOfferAcceptanceNewOrderMessage.

    (** New order for tender offer acceptance, ApplID 045. Not yet enabled. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      cl_ord_id : list byte;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (cl_ord_id_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (account_id_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (branch_id_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (order_restrictions_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (ord_type_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (order_qty_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; cl_ord_id := cl_ord_id_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TenderOfferAcceptanceNewOrderMessage.

  Module RefinancingSecuritiesLendingNonAgreedNewOrderMessage.

    (** New order for refinancing securities lending without agreement, ApplID 050. Not yet enabled. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      cl_ord_id : list byte;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
      expiration_days : N;
      expiration_type : N;
      share_property : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (expiration_days record < 256 ^ N.of_nat 2)%N /\
      (expiration_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (share_property record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_uint 2 (expiration_days record) ++
      encode_uint 1 (expiration_type record) ++
      encode_bytes 2 (share_property record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (cl_ord_id_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (account_id_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (branch_id_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (order_restrictions_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (ord_type_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (order_qty_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (expiration_days_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (expiration_type_value, bytes) =>
                                                                              match decode_bytes 2 bytes with
                                                                              | None => None
                                                                              | Some (share_property_value, bytes) =>
                                                                                  Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; cl_ord_id := cl_ord_id_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value; expiration_days := expiration_days_value; expiration_type := expiration_type_value; share_property := share_property_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 114.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefinancingSecuritiesLendingNonAgreedNewOrderMessage.

  Module OrderCancelRequestMessage.

    (** Cancels an order; the exchange does not check the original order quantity it carries. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      account_id : list byte;
      branch_id : list byte;
      order_id : list byte;
      order_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (orig_cl_ord_id record) = 10 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_id record) = 16 /\
      (order_qty record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (orig_cl_ord_id record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 16 (order_id record) ++
      encode_uint 8 (order_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (cl_ord_id_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (orig_cl_ord_id_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (account_id_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (branch_id_value, bytes) =>
                                                      match decode_bytes 16 bytes with
                                                      | None => None
                                                      | Some (order_id_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (order_qty_value, bytes) =>
                                                              Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; account_id := account_id_value; branch_id := branch_id_value; order_id := order_id_value; order_qty := order_qty_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 121.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelRequestMessage.

  Module CancelRejectMessage.

    (** Sent by the trading gateway when an order cancel request fails. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      account_id : list byte;
      branch_id : list byte;
      ord_status : list byte;
      cxl_rej_reason : N;
      reject_text : list byte;
      order_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (orig_cl_ord_id record) = 10 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (ord_status record) = 1 /\
      (cxl_rej_reason record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (reject_text record) = 16 /\
      Datatypes.length (order_id record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (orig_cl_ord_id record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 2 (cxl_rej_reason record) ++
      encode_bytes 16 (reject_text record) ++
      encode_bytes 16 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (cl_ord_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (orig_cl_ord_id_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (account_id_value, bytes) =>
                                                              match decode_bytes 2 bytes with
                                                              | None => None
                                                              | Some (branch_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (ord_status_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (cxl_rej_reason_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (reject_text_value, bytes) =>
                                                                              match decode_bytes 16 bytes with
                                                                              | None => None
                                                                              | Some (order_id_value, bytes) =>
                                                                                  Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; account_id := account_id_value; branch_id := branch_id_value; ord_status := ord_status_value; cxl_rej_reason := cxl_rej_reason_value; reject_text := reject_text_value; order_id := order_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 150.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelRejectMessage.

  Module BondSpotMatchingExecutionReportMessage.

    (** Order response and cancel execution report for spot bond trading by matching, ApplID 010: confirms or rejects a new order, a successful cancel, or an order the system cancels itself. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      order_id : list byte;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      exec_id : list byte;
      exec_type : list byte;
      ord_status : list byte;
      ord_rej_reason : N;
      leaves_qty : N;
      cum_qty : N;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
      stop_px : N;
      min_qty : N;
      max_price_levels : N;
      time_in_force : list byte;
      cash_margin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (order_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (orig_cl_ord_id record) = 10 /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (ord_status record) = 1 /\
      (ord_rej_reason record < 256 ^ N.of_nat 2)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4 /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (min_qty record < 256 ^ N.of_nat 8)%N /\
      (max_price_levels record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (time_in_force record) = 1 /\
      Datatypes.length (cash_margin record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (order_id record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (orig_cl_ord_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 2 (ord_rej_reason record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 8 (min_qty record) ++
      encode_uint 2 (max_price_levels record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_bytes 1 (cash_margin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (cl_ord_id_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (orig_cl_ord_id_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (exec_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (exec_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (ord_status_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (ord_rej_reason_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (leaves_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (cum_qty_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (ord_type_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (order_qty_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (price_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (order_restrictions_value, bytes) =>
                                                                                                                  match decode_uint 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (stop_px_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (min_qty_value, bytes) =>
                                                                                                                          match decode_uint 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (max_price_levels_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (time_in_force_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (cash_margin_value, bytes) =>
                                                                                                                                      Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; exec_type := exec_type_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value; stop_px := stop_px_value; min_qty := min_qty_value; max_price_levels := max_price_levels_value; time_in_force := time_in_force_value; cash_margin := cash_margin_value |}, bytes)
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
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 209.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 bound_31]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondSpotMatchingExecutionReportMessage.

  Module CentralizedAuctionExecutionReportMessage.

    (** Order response and cancel execution report for centralized auction stock trading, ApplID 040: confirms or rejects a new order, a successful cancel, or an order the system cancels itself. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      order_id : list byte;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      exec_id : list byte;
      exec_type : list byte;
      ord_status : list byte;
      ord_rej_reason : N;
      leaves_qty : N;
      cum_qty : N;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
      stop_px : N;
      min_qty : N;
      max_price_levels : N;
      time_in_force : list byte;
      cash_margin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (order_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (orig_cl_ord_id record) = 10 /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (ord_status record) = 1 /\
      (ord_rej_reason record < 256 ^ N.of_nat 2)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4 /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (min_qty record < 256 ^ N.of_nat 8)%N /\
      (max_price_levels record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (time_in_force record) = 1 /\
      Datatypes.length (cash_margin record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (order_id record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (orig_cl_ord_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 2 (ord_rej_reason record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 8 (min_qty record) ++
      encode_uint 2 (max_price_levels record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_bytes 1 (cash_margin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (cl_ord_id_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (orig_cl_ord_id_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (exec_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (exec_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (ord_status_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (ord_rej_reason_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (leaves_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (cum_qty_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (ord_type_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (order_qty_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (price_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (order_restrictions_value, bytes) =>
                                                                                                                  match decode_uint 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (stop_px_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (min_qty_value, bytes) =>
                                                                                                                          match decode_uint 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (max_price_levels_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (time_in_force_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (cash_margin_value, bytes) =>
                                                                                                                                      Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; exec_type := exec_type_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value; stop_px := stop_px_value; min_qty := min_qty_value; max_price_levels := max_price_levels_value; time_in_force := time_in_force_value; cash_margin := cash_margin_value |}, bytes)
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
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 209.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 bound_31]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CentralizedAuctionExecutionReportMessage.

  Module ConversionExecutionReportMessage.

    (** Order response and cancel execution report for conversion, ApplID 041: confirms or rejects a new order, a successful cancel, or an order the system cancels itself. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      order_id : list byte;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      exec_id : list byte;
      exec_type : list byte;
      ord_status : list byte;
      ord_rej_reason : N;
      leaves_qty : N;
      cum_qty : N;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (order_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (orig_cl_ord_id record) = 10 /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (ord_status record) = 1 /\
      (ord_rej_reason record < 256 ^ N.of_nat 2)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (order_id record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (orig_cl_ord_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 2 (ord_rej_reason record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (cl_ord_id_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (orig_cl_ord_id_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (exec_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (exec_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (ord_status_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (ord_rej_reason_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (leaves_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (cum_qty_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (ord_type_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (order_qty_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (price_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (order_restrictions_value, bytes) =>
                                                                                                                  Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; exec_type := exec_type_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value |}, bytes)
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
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 189.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConversionExecutionReportMessage.

  Module InquiryExecutionReportMessage.

    (** Order response and cancel execution report for inquiry, ApplID 042: confirms or rejects a new order; the business does not allow cancellation. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      order_id : list byte;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      exec_id : list byte;
      exec_type : list byte;
      ord_status : list byte;
      ord_rej_reason : N;
      leaves_qty : N;
      cum_qty : N;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (order_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (orig_cl_ord_id record) = 10 /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (ord_status record) = 1 /\
      (ord_rej_reason record < 256 ^ N.of_nat 2)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (order_id record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (orig_cl_ord_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 2 (ord_rej_reason record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (cl_ord_id_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (orig_cl_ord_id_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (exec_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (exec_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (ord_status_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (ord_rej_reason_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (leaves_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (cum_qty_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (ord_type_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (order_qty_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (price_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (order_restrictions_value, bytes) =>
                                                                                                                  Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; exec_type := exec_type_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value |}, bytes)
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
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 189.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InquiryExecutionReportMessage.

  Module SubscriptionExecutionReportMessage.

    (** Order response and cancel execution report for subscription, ApplID 043: confirms or rejects a new order; the business does not allow cancellation. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      order_id : list byte;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      exec_id : list byte;
      exec_type : list byte;
      ord_status : list byte;
      ord_rej_reason : N;
      leaves_qty : N;
      cum_qty : N;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (order_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (orig_cl_ord_id record) = 10 /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (ord_status record) = 1 /\
      (ord_rej_reason record < 256 ^ N.of_nat 2)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (order_id record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (orig_cl_ord_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 2 (ord_rej_reason record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (cl_ord_id_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (orig_cl_ord_id_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (exec_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (exec_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (ord_status_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (ord_rej_reason_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (leaves_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (cum_qty_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (ord_type_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (order_qty_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (price_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (order_restrictions_value, bytes) =>
                                                                                                                  Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; exec_type := exec_type_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value |}, bytes)
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
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 189.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SubscriptionExecutionReportMessage.

  Module PutBackExecutionReportMessage.

    (** Order response and cancel execution report for put back, ApplID 044: confirms or rejects a new order, a successful cancel, or an order the system cancels itself. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      order_id : list byte;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      exec_id : list byte;
      exec_type : list byte;
      ord_status : list byte;
      ord_rej_reason : N;
      leaves_qty : N;
      cum_qty : N;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (order_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (orig_cl_ord_id record) = 10 /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (ord_status record) = 1 /\
      (ord_rej_reason record < 256 ^ N.of_nat 2)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (order_id record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (orig_cl_ord_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 2 (ord_rej_reason record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (cl_ord_id_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (orig_cl_ord_id_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (exec_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (exec_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (ord_status_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (ord_rej_reason_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (leaves_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (cum_qty_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (ord_type_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (order_qty_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (price_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (order_restrictions_value, bytes) =>
                                                                                                                  Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; exec_type := exec_type_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value |}, bytes)
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
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 189.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PutBackExecutionReportMessage.

  Module TenderOfferAcceptanceExecutionReportMessage.

    (** Order response and cancel execution report for tender offer acceptance, ApplID 045: confirms or rejects a new order, a successful cancel, or an order the system cancels itself. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      order_id : list byte;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      exec_id : list byte;
      exec_type : list byte;
      ord_status : list byte;
      ord_rej_reason : N;
      leaves_qty : N;
      cum_qty : N;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (order_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (orig_cl_ord_id record) = 10 /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (ord_status record) = 1 /\
      (ord_rej_reason record < 256 ^ N.of_nat 2)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (order_id record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (orig_cl_ord_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 2 (ord_rej_reason record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (cl_ord_id_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (orig_cl_ord_id_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (exec_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (exec_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (ord_status_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (ord_rej_reason_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (leaves_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (cum_qty_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (ord_type_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (order_qty_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (price_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (order_restrictions_value, bytes) =>
                                                                                                                  Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; exec_type := exec_type_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value |}, bytes)
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
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 189.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TenderOfferAcceptanceExecutionReportMessage.

  Module RefinancingSecuritiesLendingNonAgreedExecutionReportMessage.

    (** Order response and cancel execution report for refinancing securities lending without agreement, ApplID 050: confirms or rejects a new order, a successful cancel, or an order the system cancels itself. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      order_id : list byte;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      exec_id : list byte;
      exec_type : list byte;
      ord_status : list byte;
      ord_rej_reason : N;
      leaves_qty : N;
      cum_qty : N;
      side : list byte;
      ord_type : list byte;
      order_qty : N;
      price : N;
      account_id : list byte;
      branch_id : list byte;
      order_restrictions : list byte;
      expiration_days : N;
      expiration_type : N;
      share_property : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (order_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (orig_cl_ord_id record) = 10 /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (ord_status record) = 1 /\
      (ord_rej_reason record < 256 ^ N.of_nat 2)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (order_restrictions record) = 4 /\
      (expiration_days record < 256 ^ N.of_nat 2)%N /\
      (expiration_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (share_property record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (order_id record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 10 (orig_cl_ord_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 2 (ord_rej_reason record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 4 (order_restrictions record) ++
      encode_uint 2 (expiration_days record) ++
      encode_uint 1 (expiration_type record) ++
      encode_bytes 2 (share_property record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (cl_ord_id_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (orig_cl_ord_id_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (exec_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (exec_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (ord_status_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (ord_rej_reason_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (leaves_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (cum_qty_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (ord_type_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (order_qty_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (price_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (order_restrictions_value, bytes) =>
                                                                                                                  match decode_uint 2 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (expiration_days_value, bytes) =>
                                                                                                                      match decode_uint 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (expiration_type_value, bytes) =>
                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (share_property_value, bytes) =>
                                                                                                                              Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; exec_type := exec_type_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; side := side_value; ord_type := ord_type_value; order_qty := order_qty_value; price := price_value; account_id := account_id_value; branch_id := branch_id_value; order_restrictions := order_restrictions_value; expiration_days := expiration_days_value; expiration_type := expiration_type_value; share_property := share_property_value |}, bytes)
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
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 194.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 bound_29]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefinancingSecuritiesLendingNonAgreedExecutionReportMessage.

  Module BondSpotMatchingTradeExecutionReportMessage.

    (** Execution report for a trade on an order for spot bond trading by matching, ApplID 010. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      order_id : list byte;
      cl_ord_id : list byte;
      exec_id : list byte;
      exec_type : list byte;
      ord_status : list byte;
      last_px : N;
      last_qty : N;
      leaves_qty : N;
      cum_qty : N;
      side : list byte;
      account_id : list byte;
      branch_id : list byte;
      cash_margin : list byte;
      settl_type : list byte;
      settl_period : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (order_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (ord_status record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (cash_margin record) = 1 /\
      Datatypes.length (settl_type record) = 1 /\
      Datatypes.length (settl_period record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (order_id record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 1 (cash_margin record) ++
      encode_bytes 1 (settl_type record) ++
      encode_bytes 1 (settl_period record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (cl_ord_id_value, bytes) =>
                                                          match decode_bytes 16 bytes with
                                                          | None => None
                                                          | Some (exec_id_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (exec_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (ord_status_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (last_px_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (last_qty_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (leaves_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (cum_qty_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_value, bytes) =>
                                                                                          match decode_bytes 10 bytes with
                                                                                          | None => None
                                                                                          | Some (account_id_value, bytes) =>
                                                                                              match decode_bytes 2 bytes with
                                                                                              | None => None
                                                                                              | Some (branch_id_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (cash_margin_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (settl_type_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (settl_period_value, bytes) =>
                                                                                                              Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; exec_type := exec_type_value; ord_status := ord_status_value; last_px := last_px_value; last_qty := last_qty_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; side := side_value; account_id := account_id_value; branch_id := branch_id_value; cash_margin := cash_margin_value; settl_type := settl_type_value; settl_period := settl_period_value |}, bytes)
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
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 175.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 bound_25]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondSpotMatchingTradeExecutionReportMessage.

  Module CentralizedAuctionTradeExecutionReportMessage.

    (** Execution report for a trade on an order for centralized auction stock trading, ApplID 040. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      order_id : list byte;
      cl_ord_id : list byte;
      exec_id : list byte;
      exec_type : list byte;
      ord_status : list byte;
      last_px : N;
      last_qty : N;
      leaves_qty : N;
      cum_qty : N;
      side : list byte;
      account_id : list byte;
      branch_id : list byte;
      cash_margin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (order_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (ord_status record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (cash_margin record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (order_id record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 1 (cash_margin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (cl_ord_id_value, bytes) =>
                                                          match decode_bytes 16 bytes with
                                                          | None => None
                                                          | Some (exec_id_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (exec_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (ord_status_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (last_px_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (last_qty_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (leaves_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (cum_qty_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_value, bytes) =>
                                                                                          match decode_bytes 10 bytes with
                                                                                          | None => None
                                                                                          | Some (account_id_value, bytes) =>
                                                                                              match decode_bytes 2 bytes with
                                                                                              | None => None
                                                                                              | Some (branch_id_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (cash_margin_value, bytes) =>
                                                                                                      Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; exec_type := exec_type_value; ord_status := ord_status_value; last_px := last_px_value; last_qty := last_qty_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; side := side_value; account_id := account_id_value; branch_id := branch_id_value; cash_margin := cash_margin_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 173.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CentralizedAuctionTradeExecutionReportMessage.

  Module RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage.

    (** Execution report for a trade on an order for refinancing securities lending without agreement, ApplID 050. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      order_id : list byte;
      cl_ord_id : list byte;
      exec_id : list byte;
      exec_type : list byte;
      ord_status : list byte;
      last_px : N;
      last_qty : N;
      leaves_qty : N;
      cum_qty : N;
      side : list byte;
      account_id : list byte;
      branch_id : list byte;
      expiration_days : N;
      expiration_type : N;
      maturity_date : N;
      share_property : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (order_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 10 /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (ord_status record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      (expiration_days record < 256 ^ N.of_nat 2)%N /\
      (expiration_type record < 256 ^ N.of_nat 1)%N /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (share_property record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (order_id record) ++
      encode_bytes 10 (cl_ord_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_uint 2 (expiration_days record) ++
      encode_uint 1 (expiration_type record) ++
      encode_uint 4 (maturity_date record) ++
      encode_bytes 2 (share_property record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (cl_ord_id_value, bytes) =>
                                                          match decode_bytes 16 bytes with
                                                          | None => None
                                                          | Some (exec_id_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (exec_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (ord_status_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (last_px_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (last_qty_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (leaves_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (cum_qty_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_value, bytes) =>
                                                                                          match decode_bytes 10 bytes with
                                                                                          | None => None
                                                                                          | Some (account_id_value, bytes) =>
                                                                                              match decode_bytes 2 bytes with
                                                                                              | None => None
                                                                                              | Some (branch_id_value, bytes) =>
                                                                                                  match decode_uint 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (expiration_days_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (expiration_type_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (maturity_date_value, bytes) =>
                                                                                                              match decode_bytes 2 bytes with
                                                                                                              | None => None
                                                                                                              | Some (share_property_value, bytes) =>
                                                                                                                  Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; exec_type := exec_type_value; ord_status := ord_status_value; last_px := last_px_value; last_qty := last_qty_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; side := side_value; account_id := account_id_value; branch_id := branch_id_value; expiration_days := expiration_days_value; expiration_type := expiration_type_value; maturity_date := maturity_date_value; share_property := share_property_value |}, bytes)
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
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 181.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefinancingSecuritiesLendingNonAgreedTradeExecutionReportMessage.

  Module BondSpotNegotiatedTradeCaptureReportMessage.

    (** Trade capture report for spot bond trading by negotiation, ApplID 031, submitted for matching. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      trade_report_ref_id : list byte;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
      member_id : list byte;
      trader_code : list byte;
      counterparty_member_id : list byte;
      counterparty_trader_code : list byte;
      settl_type : list byte;
      settl_period : list byte;
      cash_margin : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      Datatypes.length (trade_report_ref_id record) = 10 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2 /\
      Datatypes.length (member_id record) = 6 /\
      Datatypes.length (trader_code record) = 5 /\
      Datatypes.length (counterparty_member_id record) = 6 /\
      Datatypes.length (counterparty_trader_code record) = 5 /\
      Datatypes.length (settl_type record) = 1 /\
      Datatypes.length (settl_period record) = 1 /\
      Datatypes.length (cash_margin record) = 1 /\
      Datatypes.length (memo record) = 120.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_bytes 10 (trade_report_ref_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record) ++
      encode_bytes 6 (member_id record) ++
      encode_bytes 5 (trader_code record) ++
      encode_bytes 6 (counterparty_member_id record) ++
      encode_bytes 5 (counterparty_trader_code record) ++
      encode_bytes 1 (settl_type record) ++
      encode_bytes 1 (settl_period record) ++
      encode_bytes 1 (cash_margin record) ++
      encode_bytes 120 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (trade_report_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (trade_report_type_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (trade_report_trans_type_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trade_handling_instr_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_ref_id_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (last_px_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (last_qty_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (trd_type_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (trd_sub_type_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (confirm_id_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (side_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (pbuid_value, bytes) =>
                                                                                      match decode_bytes 10 bytes with
                                                                                      | None => None
                                                                                      | Some (account_id_value, bytes) =>
                                                                                          match decode_bytes 2 bytes with
                                                                                          | None => None
                                                                                          | Some (branch_id_value, bytes) =>
                                                                                              match decode_bytes 6 bytes with
                                                                                              | None => None
                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                  match decode_bytes 10 bytes with
                                                                                                  | None => None
                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                      match decode_bytes 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                          match decode_bytes 6 bytes with
                                                                                                          | None => None
                                                                                                          | Some (member_id_value, bytes) =>
                                                                                                              match decode_bytes 5 bytes with
                                                                                                              | None => None
                                                                                                              | Some (trader_code_value, bytes) =>
                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (counterparty_member_id_value, bytes) =>
                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (counterparty_trader_code_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (settl_type_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (settl_period_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (cash_margin_value, bytes) =>
                                                                                                                                      match decode_bytes 120 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (memo_value, bytes) =>
                                                                                                                                          Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; trade_report_ref_id := trade_report_ref_id_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value; member_id := member_id_value; trader_code := trader_code_value; counterparty_member_id := counterparty_member_id_value; counterparty_trader_code := counterparty_trader_code_value; settl_type := settl_type_value; settl_period := settl_period_value; cash_margin := cash_margin_value; memo := memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 294.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 bound_32]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondSpotNegotiatedTradeCaptureReportMessage.

  Module RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage.

    (** Trade capture report for refinancing securities lending by agreement, ApplID 051, submitted for matching. Not yet enabled. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      trade_report_ref_id : list byte;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
      expiration_days : N;
      expiration_type : N;
      share_property : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      Datatypes.length (trade_report_ref_id record) = 10 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2 /\
      (expiration_days record < 256 ^ N.of_nat 2)%N /\
      (expiration_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (share_property record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_bytes 10 (trade_report_ref_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record) ++
      encode_uint 2 (expiration_days record) ++
      encode_uint 1 (expiration_type record) ++
      encode_bytes 2 (share_property record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (trade_report_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (trade_report_type_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (trade_report_trans_type_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trade_handling_instr_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_ref_id_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (last_px_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (last_qty_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (trd_type_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (trd_sub_type_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (confirm_id_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (side_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (pbuid_value, bytes) =>
                                                                                      match decode_bytes 10 bytes with
                                                                                      | None => None
                                                                                      | Some (account_id_value, bytes) =>
                                                                                          match decode_bytes 2 bytes with
                                                                                          | None => None
                                                                                          | Some (branch_id_value, bytes) =>
                                                                                              match decode_bytes 6 bytes with
                                                                                              | None => None
                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                  match decode_bytes 10 bytes with
                                                                                                  | None => None
                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                      match decode_bytes 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                          match decode_uint 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (expiration_days_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (expiration_type_value, bytes) =>
                                                                                                                  match decode_bytes 2 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (share_property_value, bytes) =>
                                                                                                                      Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; trade_report_ref_id := trade_report_ref_id_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value; expiration_days := expiration_days_value; expiration_type := expiration_type_value; share_property := share_property_value |}, bytes)
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
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 154.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefinancingSecuritiesLendingAgreedTradeCaptureReportMessage.

  Module MutualTradeConfirmationTradeCaptureReportMessage.

    (** Trade capture report for mutual trade confirmation, ApplID 060, submitted for matching. Not yet enabled. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      trade_report_ref_id : list byte;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      Datatypes.length (trade_report_ref_id record) = 10 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_bytes 10 (trade_report_ref_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (trade_report_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (trade_report_type_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (trade_report_trans_type_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trade_handling_instr_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_ref_id_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (last_px_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (last_qty_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (trd_type_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (trd_sub_type_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (confirm_id_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (side_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (pbuid_value, bytes) =>
                                                                                      match decode_bytes 10 bytes with
                                                                                      | None => None
                                                                                      | Some (account_id_value, bytes) =>
                                                                                          match decode_bytes 2 bytes with
                                                                                          | None => None
                                                                                          | Some (branch_id_value, bytes) =>
                                                                                              match decode_bytes 6 bytes with
                                                                                              | None => None
                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                  match decode_bytes 10 bytes with
                                                                                                  | None => None
                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                      match decode_bytes 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                          Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; trade_report_ref_id := trade_report_ref_id_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value |}, bytes)
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
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 149.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MutualTradeConfirmationTradeCaptureReportMessage.

  Module MarketMakingMutualTradeConfirmationTradeCaptureReportMessage.

    (** Trade capture report for market making mutual trade confirmation, ApplID 061, submitted for matching. Not yet enabled. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      trade_report_ref_id : list byte;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      Datatypes.length (trade_report_ref_id record) = 10 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_bytes 10 (trade_report_ref_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (trade_report_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (trade_report_type_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (trade_report_trans_type_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trade_handling_instr_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_ref_id_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (last_px_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (last_qty_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (trd_type_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (trd_sub_type_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (confirm_id_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (side_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (pbuid_value, bytes) =>
                                                                                      match decode_bytes 10 bytes with
                                                                                      | None => None
                                                                                      | Some (account_id_value, bytes) =>
                                                                                          match decode_bytes 2 bytes with
                                                                                          | None => None
                                                                                          | Some (branch_id_value, bytes) =>
                                                                                              match decode_bytes 6 bytes with
                                                                                              | None => None
                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                  match decode_bytes 10 bytes with
                                                                                                  | None => None
                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                      match decode_bytes 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                          Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; trade_report_ref_id := trade_report_ref_id_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value |}, bytes)
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
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 149.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketMakingMutualTradeConfirmationTradeCaptureReportMessage.

  Module AfterHoursBlockTradeTradeCaptureReportMessage.

    (** Trade capture report for after hours block trading, ApplID 062, submitted for matching. Not yet enabled. *)
    Record t := {
      appl_id : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      trade_report_ref_id : list byte;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
      cash_margin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      Datatypes.length (trade_report_ref_id record) = 10 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2 /\
      Datatypes.length (cash_margin record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_bytes 10 (trade_report_ref_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record) ++
      encode_bytes 1 (cash_margin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (appl_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (submitting_pbuid_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (security_id_source_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (owner_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (user_info_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (trade_report_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (trade_report_type_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (trade_report_trans_type_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trade_handling_instr_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_ref_id_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (last_px_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (last_qty_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (trd_type_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (trd_sub_type_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (confirm_id_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (side_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (pbuid_value, bytes) =>
                                                                                      match decode_bytes 10 bytes with
                                                                                      | None => None
                                                                                      | Some (account_id_value, bytes) =>
                                                                                          match decode_bytes 2 bytes with
                                                                                          | None => None
                                                                                          | Some (branch_id_value, bytes) =>
                                                                                              match decode_bytes 6 bytes with
                                                                                              | None => None
                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                  match decode_bytes 10 bytes with
                                                                                                  | None => None
                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                      match decode_bytes 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (cash_margin_value, bytes) =>
                                                                                                              Some ({| appl_id := appl_id_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; trade_report_ref_id := trade_report_ref_id_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value; cash_margin := cash_margin_value |}, bytes)
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
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 150.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 bound_25]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AfterHoursBlockTradeTradeCaptureReportMessage.

  Module BondSpotNegotiatedTradeCaptureReportAckMessage.

    (** Trading gateway response to a trade capture report for spot bond trading by negotiation, ApplID 031. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_id : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      trade_report_ref_id : list byte;
      trd_ack_status : N;
      trd_rpt_status : N;
      trade_report_reject_reason : N;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      exec_id : list byte;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
      member_id : list byte;
      trader_code : list byte;
      counterparty_member_id : list byte;
      counterparty_trader_code : list byte;
      settl_type : list byte;
      settl_period : list byte;
      cash_margin : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_id record) = 16 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      Datatypes.length (trade_report_ref_id record) = 10 /\
      (trd_ack_status record < 256 ^ N.of_nat 1)%N /\
      (trd_rpt_status record < 256 ^ N.of_nat 1)%N /\
      (trade_report_reject_reason record < 256 ^ N.of_nat 2)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2 /\
      Datatypes.length (member_id record) = 6 /\
      Datatypes.length (trader_code record) = 5 /\
      Datatypes.length (counterparty_member_id record) = 6 /\
      Datatypes.length (counterparty_trader_code record) = 5 /\
      Datatypes.length (settl_type record) = 1 /\
      Datatypes.length (settl_period record) = 1 /\
      Datatypes.length (cash_margin record) = 1 /\
      Datatypes.length (memo record) = 120.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (trade_id record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_bytes 10 (trade_report_ref_id record) ++
      encode_uint 1 (trd_ack_status record) ++
      encode_uint 1 (trd_rpt_status record) ++
      encode_uint 2 (trade_report_reject_reason record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record) ++
      encode_bytes 6 (member_id record) ++
      encode_bytes 5 (trader_code record) ++
      encode_bytes 6 (counterparty_member_id record) ++
      encode_bytes 5 (counterparty_trader_code record) ++
      encode_bytes 1 (settl_type record) ++
      encode_bytes 1 (settl_period record) ++
      encode_bytes 1 (cash_margin record) ++
      encode_bytes 120 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (trade_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (trade_report_type_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (trade_report_trans_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_handling_instr_value, bytes) =>
                                                                      match decode_bytes 10 bytes with
                                                                      | None => None
                                                                      | Some (trade_report_ref_id_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (trd_ack_status_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (trd_rpt_status_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_report_reject_reason_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (last_px_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (last_qty_value, bytes) =>
                                                                                              match decode_uint 2 bytes with
                                                                                              | None => None
                                                                                              | Some (trd_type_value, bytes) =>
                                                                                                  match decode_uint 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trd_sub_type_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (confirm_id_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (exec_id_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (side_value, bytes) =>
                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (pbuid_value, bytes) =>
                                                                                                                      match decode_bytes 10 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                                              match decode_bytes 6 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                                                          match decode_bytes 6 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (member_id_value, bytes) =>
                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (trader_code_value, bytes) =>
                                                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (counterparty_member_id_value, bytes) =>
                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (counterparty_trader_code_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (settl_type_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (settl_period_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (cash_margin_value, bytes) =>
                                                                                                                                                                      match decode_bytes 120 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (memo_value, bytes) =>
                                                                                                                                                                          Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_id := trade_id_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; trade_report_ref_id := trade_report_ref_id_value; trd_ack_status := trd_ack_status_value; trd_rpt_status := trd_rpt_status_value; trade_report_reject_reason := trade_report_reject_reason_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; exec_id := exec_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value; member_id := member_id_value; trader_code := trader_code_value; counterparty_member_id := counterparty_member_id_value; counterparty_trader_code := counterparty_trader_code_value; settl_type := settl_type_value; settl_period := settl_period_value; cash_margin := cash_margin_value; memo := memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 348.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 bound_40]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondSpotNegotiatedTradeCaptureReportAckMessage.

  Module RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage.

    (** Trading gateway response to a trade capture report for refinancing securities lending by agreement, ApplID 051. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_id : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      trade_report_ref_id : list byte;
      trd_ack_status : N;
      trd_rpt_status : N;
      trade_report_reject_reason : N;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      exec_id : list byte;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
      expiration_days : N;
      expiration_type : N;
      share_property : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_id record) = 16 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      Datatypes.length (trade_report_ref_id record) = 10 /\
      (trd_ack_status record < 256 ^ N.of_nat 1)%N /\
      (trd_rpt_status record < 256 ^ N.of_nat 1)%N /\
      (trade_report_reject_reason record < 256 ^ N.of_nat 2)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2 /\
      (expiration_days record < 256 ^ N.of_nat 2)%N /\
      (expiration_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (share_property record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (trade_id record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_bytes 10 (trade_report_ref_id record) ++
      encode_uint 1 (trd_ack_status record) ++
      encode_uint 1 (trd_rpt_status record) ++
      encode_uint 2 (trade_report_reject_reason record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record) ++
      encode_uint 2 (expiration_days record) ++
      encode_uint 1 (expiration_type record) ++
      encode_bytes 2 (share_property record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (trade_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (trade_report_type_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (trade_report_trans_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_handling_instr_value, bytes) =>
                                                                      match decode_bytes 10 bytes with
                                                                      | None => None
                                                                      | Some (trade_report_ref_id_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (trd_ack_status_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (trd_rpt_status_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_report_reject_reason_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (last_px_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (last_qty_value, bytes) =>
                                                                                              match decode_uint 2 bytes with
                                                                                              | None => None
                                                                                              | Some (trd_type_value, bytes) =>
                                                                                                  match decode_uint 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trd_sub_type_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (confirm_id_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (exec_id_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (side_value, bytes) =>
                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (pbuid_value, bytes) =>
                                                                                                                      match decode_bytes 10 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                                              match decode_bytes 6 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                                                          match decode_uint 2 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (expiration_days_value, bytes) =>
                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (expiration_type_value, bytes) =>
                                                                                                                                                  match decode_bytes 2 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (share_property_value, bytes) =>
                                                                                                                                                      Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_id := trade_id_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; trade_report_ref_id := trade_report_ref_id_value; trd_ack_status := trd_ack_status_value; trd_rpt_status := trd_rpt_status_value; trade_report_reject_reason := trade_report_reject_reason_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; exec_id := exec_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value; expiration_days := expiration_days_value; expiration_type := expiration_type_value; share_property := share_property_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 208.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 bound_35]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefinancingSecuritiesLendingAgreedTradeCaptureReportAckMessage.

  Module MutualTradeConfirmationTradeCaptureReportAckMessage.

    (** Trading gateway response to a trade capture report for mutual trade confirmation, ApplID 060. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_id : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      trade_report_ref_id : list byte;
      trd_ack_status : N;
      trd_rpt_status : N;
      trade_report_reject_reason : N;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      exec_id : list byte;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_id record) = 16 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      Datatypes.length (trade_report_ref_id record) = 10 /\
      (trd_ack_status record < 256 ^ N.of_nat 1)%N /\
      (trd_rpt_status record < 256 ^ N.of_nat 1)%N /\
      (trade_report_reject_reason record < 256 ^ N.of_nat 2)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (trade_id record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_bytes 10 (trade_report_ref_id record) ++
      encode_uint 1 (trd_ack_status record) ++
      encode_uint 1 (trd_rpt_status record) ++
      encode_uint 2 (trade_report_reject_reason record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (trade_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (trade_report_type_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (trade_report_trans_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_handling_instr_value, bytes) =>
                                                                      match decode_bytes 10 bytes with
                                                                      | None => None
                                                                      | Some (trade_report_ref_id_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (trd_ack_status_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (trd_rpt_status_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_report_reject_reason_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (last_px_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (last_qty_value, bytes) =>
                                                                                              match decode_uint 2 bytes with
                                                                                              | None => None
                                                                                              | Some (trd_type_value, bytes) =>
                                                                                                  match decode_uint 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trd_sub_type_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (confirm_id_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (exec_id_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (side_value, bytes) =>
                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (pbuid_value, bytes) =>
                                                                                                                      match decode_bytes 10 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                                              match decode_bytes 6 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                                                          Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_id := trade_id_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; trade_report_ref_id := trade_report_ref_id_value; trd_ack_status := trd_ack_status_value; trd_rpt_status := trd_rpt_status_value; trade_report_reject_reason := trade_report_reject_reason_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; exec_id := exec_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 203.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 bound_32]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MutualTradeConfirmationTradeCaptureReportAckMessage.

  Module MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage.

    (** Trading gateway response to a trade capture report for market making mutual trade confirmation, ApplID 061. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_id : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      trade_report_ref_id : list byte;
      trd_ack_status : N;
      trd_rpt_status : N;
      trade_report_reject_reason : N;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      exec_id : list byte;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_id record) = 16 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      Datatypes.length (trade_report_ref_id record) = 10 /\
      (trd_ack_status record < 256 ^ N.of_nat 1)%N /\
      (trd_rpt_status record < 256 ^ N.of_nat 1)%N /\
      (trade_report_reject_reason record < 256 ^ N.of_nat 2)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (trade_id record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_bytes 10 (trade_report_ref_id record) ++
      encode_uint 1 (trd_ack_status record) ++
      encode_uint 1 (trd_rpt_status record) ++
      encode_uint 2 (trade_report_reject_reason record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (trade_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (trade_report_type_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (trade_report_trans_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_handling_instr_value, bytes) =>
                                                                      match decode_bytes 10 bytes with
                                                                      | None => None
                                                                      | Some (trade_report_ref_id_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (trd_ack_status_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (trd_rpt_status_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_report_reject_reason_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (last_px_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (last_qty_value, bytes) =>
                                                                                              match decode_uint 2 bytes with
                                                                                              | None => None
                                                                                              | Some (trd_type_value, bytes) =>
                                                                                                  match decode_uint 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trd_sub_type_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (confirm_id_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (exec_id_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (side_value, bytes) =>
                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (pbuid_value, bytes) =>
                                                                                                                      match decode_bytes 10 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                                              match decode_bytes 6 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                                                          Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_id := trade_id_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; trade_report_ref_id := trade_report_ref_id_value; trd_ack_status := trd_ack_status_value; trd_rpt_status := trd_rpt_status_value; trade_report_reject_reason := trade_report_reject_reason_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; exec_id := exec_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 203.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 bound_32]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketMakingMutualTradeConfirmationTradeCaptureReportAckMessage.

  Module AfterHoursBlockTradeTradeCaptureReportAckMessage.

    (** Trading gateway response to a trade capture report for after hours block trading, ApplID 062. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_id : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      trade_report_ref_id : list byte;
      trd_ack_status : N;
      trd_rpt_status : N;
      trade_report_reject_reason : N;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      exec_id : list byte;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
      cash_margin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_id record) = 16 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      Datatypes.length (trade_report_ref_id record) = 10 /\
      (trd_ack_status record < 256 ^ N.of_nat 1)%N /\
      (trd_rpt_status record < 256 ^ N.of_nat 1)%N /\
      (trade_report_reject_reason record < 256 ^ N.of_nat 2)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2 /\
      Datatypes.length (cash_margin record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (trade_id record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_bytes 10 (trade_report_ref_id record) ++
      encode_uint 1 (trd_ack_status record) ++
      encode_uint 1 (trd_rpt_status record) ++
      encode_uint 2 (trade_report_reject_reason record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record) ++
      encode_bytes 1 (cash_margin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (trade_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (trade_report_type_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (trade_report_trans_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_handling_instr_value, bytes) =>
                                                                      match decode_bytes 10 bytes with
                                                                      | None => None
                                                                      | Some (trade_report_ref_id_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (trd_ack_status_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (trd_rpt_status_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_report_reject_reason_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (last_px_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (last_qty_value, bytes) =>
                                                                                              match decode_uint 2 bytes with
                                                                                              | None => None
                                                                                              | Some (trd_type_value, bytes) =>
                                                                                                  match decode_uint 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trd_sub_type_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (confirm_id_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (exec_id_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (side_value, bytes) =>
                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (pbuid_value, bytes) =>
                                                                                                                      match decode_bytes 10 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                                              match decode_bytes 6 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (cash_margin_value, bytes) =>
                                                                                                                                              Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_id := trade_id_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; trade_report_ref_id := trade_report_ref_id_value; trd_ack_status := trd_ack_status_value; trd_rpt_status := trd_rpt_status_value; trade_report_reject_reason := trade_report_reject_reason_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; exec_id := exec_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value; cash_margin := cash_margin_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 204.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 bound_33]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AfterHoursBlockTradeTradeCaptureReportAckMessage.

  Module BondSpotNegotiatedTradeCaptureReportConfirmationMessage.

    (** Trade confirmation of a trade capture report for spot bond trading by negotiation, ApplID 031. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_id : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      exec_id : list byte;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
      member_id : list byte;
      trader_code : list byte;
      counterparty_member_id : list byte;
      counterparty_trader_code : list byte;
      settl_type : list byte;
      settl_period : list byte;
      cash_margin : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_id record) = 16 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2 /\
      Datatypes.length (member_id record) = 6 /\
      Datatypes.length (trader_code record) = 5 /\
      Datatypes.length (counterparty_member_id record) = 6 /\
      Datatypes.length (counterparty_trader_code record) = 5 /\
      Datatypes.length (settl_type record) = 1 /\
      Datatypes.length (settl_period record) = 1 /\
      Datatypes.length (cash_margin record) = 1 /\
      Datatypes.length (memo record) = 120.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (trade_id record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record) ++
      encode_bytes 6 (member_id record) ++
      encode_bytes 5 (trader_code record) ++
      encode_bytes 6 (counterparty_member_id record) ++
      encode_bytes 5 (counterparty_trader_code record) ++
      encode_bytes 1 (settl_type record) ++
      encode_bytes 1 (settl_period record) ++
      encode_bytes 1 (cash_margin record) ++
      encode_bytes 120 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (trade_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (trade_report_type_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (trade_report_trans_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_handling_instr_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (last_px_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (last_qty_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (trd_type_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (trd_sub_type_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (confirm_id_value, bytes) =>
                                                                                          match decode_bytes 16 bytes with
                                                                                          | None => None
                                                                                          | Some (exec_id_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (side_value, bytes) =>
                                                                                                  match decode_bytes 6 bytes with
                                                                                                  | None => None
                                                                                                  | Some (pbuid_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 6 bytes with
                                                                                                              | None => None
                                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                                          match decode_bytes 6 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (member_id_value, bytes) =>
                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (trader_code_value, bytes) =>
                                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (counterparty_member_id_value, bytes) =>
                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (counterparty_trader_code_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (settl_type_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (settl_period_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (cash_margin_value, bytes) =>
                                                                                                                                                      match decode_bytes 120 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (memo_value, bytes) =>
                                                                                                                                                          Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_id := trade_id_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; exec_id := exec_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value; member_id := member_id_value; trader_code := trader_code_value; counterparty_member_id := counterparty_member_id_value; counterparty_trader_code := counterparty_trader_code_value; settl_type := settl_type_value; settl_period := settl_period_value; cash_margin := cash_margin_value; memo := memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 334.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 bound_36]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondSpotNegotiatedTradeCaptureReportConfirmationMessage.

  Module RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage.

    (** Trade confirmation of a trade capture report for refinancing securities lending by agreement, ApplID 051. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_id : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      exec_id : list byte;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
      expiration_days : N;
      expiration_type : N;
      maturity_date : N;
      share_property : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_id record) = 16 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2 /\
      (expiration_days record < 256 ^ N.of_nat 2)%N /\
      (expiration_type record < 256 ^ N.of_nat 1)%N /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (share_property record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (trade_id record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record) ++
      encode_uint 2 (expiration_days record) ++
      encode_uint 1 (expiration_type record) ++
      encode_uint 4 (maturity_date record) ++
      encode_bytes 2 (share_property record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (trade_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (trade_report_type_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (trade_report_trans_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_handling_instr_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (last_px_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (last_qty_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (trd_type_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (trd_sub_type_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (confirm_id_value, bytes) =>
                                                                                          match decode_bytes 16 bytes with
                                                                                          | None => None
                                                                                          | Some (exec_id_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (side_value, bytes) =>
                                                                                                  match decode_bytes 6 bytes with
                                                                                                  | None => None
                                                                                                  | Some (pbuid_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 6 bytes with
                                                                                                              | None => None
                                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                                          match decode_uint 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (expiration_days_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (expiration_type_value, bytes) =>
                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (maturity_date_value, bytes) =>
                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (share_property_value, bytes) =>
                                                                                                                                          Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_id := trade_id_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; exec_id := exec_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value; expiration_days := expiration_days_value; expiration_type := expiration_type_value; maturity_date := maturity_date_value; share_property := share_property_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 198.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 bound_32]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefinancingSecuritiesLendingAgreedTradeCaptureReportConfirmationMessage.

  Module MutualTradeConfirmationTradeCaptureReportConfirmationMessage.

    (** Trade confirmation of a trade capture report for mutual trade confirmation, ApplID 060. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_id : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      exec_id : list byte;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_id record) = 16 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (trade_id record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (trade_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (trade_report_type_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (trade_report_trans_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_handling_instr_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (last_px_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (last_qty_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (trd_type_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (trd_sub_type_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (confirm_id_value, bytes) =>
                                                                                          match decode_bytes 16 bytes with
                                                                                          | None => None
                                                                                          | Some (exec_id_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (side_value, bytes) =>
                                                                                                  match decode_bytes 6 bytes with
                                                                                                  | None => None
                                                                                                  | Some (pbuid_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 6 bytes with
                                                                                                              | None => None
                                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                                          Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_id := trade_id_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; exec_id := exec_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value |}, bytes)
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
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 189.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 bound_28]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MutualTradeConfirmationTradeCaptureReportConfirmationMessage.

  Module MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage.

    (** Trade confirmation of a trade capture report for market making mutual trade confirmation, ApplID 061. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_id : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      exec_id : list byte;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_id record) = 16 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (trade_id record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (trade_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (trade_report_type_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (trade_report_trans_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_handling_instr_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (last_px_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (last_qty_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (trd_type_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (trd_sub_type_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (confirm_id_value, bytes) =>
                                                                                          match decode_bytes 16 bytes with
                                                                                          | None => None
                                                                                          | Some (exec_id_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (side_value, bytes) =>
                                                                                                  match decode_bytes 6 bytes with
                                                                                                  | None => None
                                                                                                  | Some (pbuid_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 6 bytes with
                                                                                                              | None => None
                                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                                          Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_id := trade_id_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; exec_id := exec_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value |}, bytes)
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
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 189.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 bound_28]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketMakingMutualTradeConfirmationTradeCaptureReportConfirmationMessage.

  Module AfterHoursBlockTradeTradeCaptureReportConfirmationMessage.

    (** Trade confirmation of a trade capture report for after hours block trading, ApplID 062. Not yet enabled. *)
    Record t := {
      partition_no : N;
      report_index : N;
      appl_id : list byte;
      reporting_pbuid : list byte;
      submitting_pbuid : list byte;
      security_id : list byte;
      security_id_source : list byte;
      owner_type : N;
      clearing_firm : list byte;
      transact_time : N;
      user_info : list byte;
      trade_id : list byte;
      trade_report_id : list byte;
      trade_report_type : N;
      trade_report_trans_type : N;
      trade_handling_instr : list byte;
      last_px : N;
      last_qty : N;
      trd_type : N;
      trd_sub_type : N;
      confirm_id : N;
      exec_id : list byte;
      side : list byte;
      pbuid : list byte;
      account_id : list byte;
      branch_id : list byte;
      counterparty_pbuid : list byte;
      counterparty_account_id : list byte;
      counterparty_branch_id : list byte;
      cash_margin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_no record < 256 ^ N.of_nat 4)%N /\
      (report_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (appl_id record) = 3 /\
      Datatypes.length (reporting_pbuid record) = 6 /\
      Datatypes.length (submitting_pbuid record) = 6 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (security_id_source record) = 4 /\
      (owner_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_firm record) = 2 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (user_info record) = 32 /\
      Datatypes.length (trade_id record) = 16 /\
      Datatypes.length (trade_report_id record) = 10 /\
      (trade_report_type record < 256 ^ N.of_nat 1)%N /\
      (trade_report_trans_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_handling_instr record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 8)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (trd_sub_type record < 256 ^ N.of_nat 2)%N /\
      (confirm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_id record) = 16 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (pbuid record) = 6 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (branch_id record) = 2 /\
      Datatypes.length (counterparty_pbuid record) = 6 /\
      Datatypes.length (counterparty_account_id record) = 10 /\
      Datatypes.length (counterparty_branch_id record) = 2 /\
      Datatypes.length (cash_margin record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (partition_no record) ++
      encode_uint 8 (report_index record) ++
      encode_bytes 3 (appl_id record) ++
      encode_bytes 6 (reporting_pbuid record) ++
      encode_bytes 6 (submitting_pbuid record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 4 (security_id_source record) ++
      encode_uint 2 (owner_type record) ++
      encode_bytes 2 (clearing_firm record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 32 (user_info record) ++
      encode_bytes 16 (trade_id record) ++
      encode_bytes 10 (trade_report_id record) ++
      encode_uint 1 (trade_report_type record) ++
      encode_uint 1 (trade_report_trans_type record) ++
      encode_bytes 1 (trade_handling_instr record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (last_qty record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (trd_sub_type record) ++
      encode_uint 4 (confirm_id record) ++
      encode_bytes 16 (exec_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (pbuid record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 2 (branch_id record) ++
      encode_bytes 6 (counterparty_pbuid record) ++
      encode_bytes 10 (counterparty_account_id record) ++
      encode_bytes 2 (counterparty_branch_id record) ++
      encode_bytes 1 (cash_margin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (partition_no_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (report_index_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (appl_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (reporting_pbuid_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (submitting_pbuid_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (security_id_source_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (owner_type_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (user_info_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (trade_id_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (trade_report_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (trade_report_type_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (trade_report_trans_type_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_handling_instr_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (last_px_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (last_qty_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (trd_type_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (trd_sub_type_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (confirm_id_value, bytes) =>
                                                                                          match decode_bytes 16 bytes with
                                                                                          | None => None
                                                                                          | Some (exec_id_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (side_value, bytes) =>
                                                                                                  match decode_bytes 6 bytes with
                                                                                                  | None => None
                                                                                                  | Some (pbuid_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                          match decode_bytes 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (branch_id_value, bytes) =>
                                                                                                              match decode_bytes 6 bytes with
                                                                                                              | None => None
                                                                                                              | Some (counterparty_pbuid_value, bytes) =>
                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (counterparty_account_id_value, bytes) =>
                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (counterparty_branch_id_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (cash_margin_value, bytes) =>
                                                                                                                              Some ({| partition_no := partition_no_value; report_index := report_index_value; appl_id := appl_id_value; reporting_pbuid := reporting_pbuid_value; submitting_pbuid := submitting_pbuid_value; security_id := security_id_value; security_id_source := security_id_source_value; owner_type := owner_type_value; clearing_firm := clearing_firm_value; transact_time := transact_time_value; user_info := user_info_value; trade_id := trade_id_value; trade_report_id := trade_report_id_value; trade_report_type := trade_report_type_value; trade_report_trans_type := trade_report_trans_type_value; trade_handling_instr := trade_handling_instr_value; last_px := last_px_value; last_qty := last_qty_value; trd_type := trd_type_value; trd_sub_type := trd_sub_type_value; confirm_id := confirm_id_value; exec_id := exec_id_value; side := side_value; pbuid := pbuid_value; account_id := account_id_value; branch_id := branch_id_value; counterparty_pbuid := counterparty_pbuid_value; counterparty_account_id := counterparty_account_id_value; counterparty_branch_id := counterparty_branch_id_value; cash_margin := cash_margin_value |}, bytes)
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
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 190.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 bound_29]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AfterHoursBlockTradeTradeCaptureReportConfirmationMessage.

  Module MessageTail.

    (** Bjse Bjtg Message Tail, defining the checksum of a message, transmitted without encryption *)
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

End NeeqSecuritiesOrderEntryV11.
