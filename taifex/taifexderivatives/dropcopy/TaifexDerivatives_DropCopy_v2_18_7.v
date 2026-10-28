From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Taiwan Futures Exchange Drop Copy Service

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
      - a Composite rule
      - the dispatch that chooses a message by its type
      - a run counted by a field
  *)

Module TaifexDerivativesDropCopyV2187.

  Module WakeUpCallMessage.

    (** Wake up call message, which either Taifex or the futures commission merchant may initiate in the logon phase of the Link Subsystem. *)
    Record t := {
      status_code_uint_81 : N;
      start_in_bound_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (status_code_uint_81 record < 256 ^ N.of_nat 1)%N /\
      (start_in_bound_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (status_code_uint_81 record) ++
      encode_uint 4 (start_in_bound_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (status_code_uint_81_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (start_in_bound_num_value, bytes) =>
              Some ({| status_code_uint_81 := status_code_uint_81_value; start_in_bound_num := start_in_bound_num_value |}, bytes)
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

  End WakeUpCallMessage.

  Module WakeUpCallConfirmedMessage.

    (** Wake up call confirmed message, sent by the futures commission merchant to Taifex. *)
    Record t := {
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (version record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (version_value, bytes) =>
          Some ({| version := version_value |}, bytes)
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

  End WakeUpCallConfirmedMessage.

  Module LogonNoticeMessage.

    (** Logon notice message, carrying the sequence No of the last message Taifex sent the futures commission merchant in the session. *)
    Record t := {
      status_code_uint_81 : N;
      append_no : N;
      end_out_bound_num : N;
      system_type : N;
      encrypt_method : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (status_code_uint_81 record < 256 ^ N.of_nat 1)%N /\
      (append_no record < 256 ^ N.of_nat 2)%N /\
      (end_out_bound_num record < 256 ^ N.of_nat 4)%N /\
      (system_type record < 256 ^ N.of_nat 1)%N /\
      (encrypt_method record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (status_code_uint_81 record) ++
      encode_uint 2 (append_no record) ++
      encode_uint 4 (end_out_bound_num record) ++
      encode_uint 1 (system_type record) ++
      encode_uint 1 (encrypt_method record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (status_code_uint_81_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (append_no_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (end_out_bound_num_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (system_type_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (encrypt_method_value, bytes) =>
                          Some ({| status_code_uint_81 := status_code_uint_81_value; append_no := append_no_value; end_out_bound_num := end_out_bound_num_value; system_type := system_type_value; encrypt_method := encrypt_method_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End LogonNoticeMessage.

  Module SubHdr.

    (** Tmp Expanded Message Header, which assigns different functionalities to a MessageType by defining additional subcategories for it *)
    Record t := {
      msg_type_ext : N;
      preserve : N;
      msg_time_ns : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_type_ext record < 256 ^ N.of_nat 1)%N /\
      (preserve record < 256 ^ N.of_nat 1)%N /\
      (msg_time_ns record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (msg_type_ext record) ++
      encode_uint 1 (preserve record) ++
      encode_uint 4 (msg_time_ns record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (msg_type_ext_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (preserve_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_time_ns_value, bytes) =>
                  Some ({| msg_type_ext := msg_type_ext_value; preserve := preserve_value; msg_time_ns := msg_time_ns_value |}, bytes)
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

  End SubHdr.

  Module FinalSequentialNumberNotificationForGroupMessage.

    (** Final Sequential Number Notification Message for Group, transmitting the group's last report sequence number to the futures commission merchant. *)
    Record t := {
      sub_hdr : SubHdr.t;
      status_code_uint_162 : N;
      part_id : N;
      end_out_bound_num : N;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SubHdr.bounded (sub_hdr record) /\
      (status_code_uint_162 record < 256 ^ N.of_nat 2)%N /\
      (part_id record < 256 ^ N.of_nat 1)%N /\
      (end_out_bound_num record < 256 ^ N.of_nat 4)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      SubHdr.encode (sub_hdr record) ++
      encode_uint 2 (status_code_uint_162 record) ++
      encode_uint 1 (part_id record) ++
      encode_uint 4 (end_out_bound_num record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SubHdr.decode bytes with
      | None => None
      | Some (sub_hdr_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (status_code_uint_162_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (part_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (end_out_bound_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (reserved_8_value, bytes) =>
                          Some ({| sub_hdr := sub_hdr_value; status_code_uint_162 := status_code_uint_162_value; part_id := part_id_value; end_out_bound_num := end_out_bound_num_value; reserved_8 := reserved_8_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SubHdr.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SubHdr.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply SubHdr.eq_dec]. Defined.

  End FinalSequentialNumberNotificationForGroupMessage.

  Module RequestLogonMessage.

    (** Request logon, sent by the futures commission merchant to Taifex with the start sequence of the messages it requests Taifex to resend. *)
    Record t := {
      status_code_uint_81 : N;
      append_no : N;
      fcm_id : N;
      session_id : N;
      system_type : N;
      ap_code : N;
      key_value : N;
      request_start_seq : N;
      cancel_order_sec : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (status_code_uint_81 record < 256 ^ N.of_nat 1)%N /\
      (append_no record < 256 ^ N.of_nat 2)%N /\
      (fcm_id record < 256 ^ N.of_nat 2)%N /\
      (session_id record < 256 ^ N.of_nat 2)%N /\
      (system_type record < 256 ^ N.of_nat 1)%N /\
      (ap_code record < 256 ^ N.of_nat 1)%N /\
      (key_value record < 256 ^ N.of_nat 1)%N /\
      (request_start_seq record < 256 ^ N.of_nat 4)%N /\
      (cancel_order_sec record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (status_code_uint_81 record) ++
      encode_uint 2 (append_no record) ++
      encode_uint 2 (fcm_id record) ++
      encode_uint 2 (session_id record) ++
      encode_uint 1 (system_type record) ++
      encode_uint 1 (ap_code record) ++
      encode_uint 1 (key_value record) ++
      encode_uint 4 (request_start_seq record) ++
      encode_uint 1 (cancel_order_sec record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (status_code_uint_81_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (append_no_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (fcm_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (session_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (system_type_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (ap_code_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (key_value_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (request_start_seq_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (cancel_order_sec_value, bytes) =>
                                          Some ({| status_code_uint_81 := status_code_uint_81_value; append_no := append_no_value; fcm_id := fcm_id_value; session_id := session_id_value; system_type := system_type_value; ap_code := ap_code_value; key_value := key_value_value; request_start_seq := request_start_seq_value; cancel_order_sec := cancel_order_sec_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RequestLogonMessage.

  Module ActivateApplicationSystemMessage.

    (** Activate application system, sent by Taifex to the futures commission merchant. *)
    Record t := {
      status_code_uint_81 : N;
      heart_bt_int : N;
      max_flow_ctrl_cnt : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (status_code_uint_81 record < 256 ^ N.of_nat 1)%N /\
      (heart_bt_int record < 256 ^ N.of_nat 1)%N /\
      (max_flow_ctrl_cnt record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (status_code_uint_81 record) ++
      encode_uint 1 (heart_bt_int record) ++
      encode_uint 2 (max_flow_ctrl_cnt record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (status_code_uint_81_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (heart_bt_int_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (max_flow_ctrl_cnt_value, bytes) =>
                  Some ({| status_code_uint_81 := status_code_uint_81_value; heart_bt_int := heart_bt_int_value; max_flow_ctrl_cnt := max_flow_ctrl_cnt_value |}, bytes)
              end
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

  End ActivateApplicationSystemMessage.

  Module ActivateApplicationSystemConfirmedMessage.

    (** Activate application system confirmed, from which Taifex calculates the round trip time of the L50 message to determine the maximum peak flow per second. *)
    Record t := {
      status_code_uint_81 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (status_code_uint_81 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (status_code_uint_81 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (status_code_uint_81_value, bytes) =>
          Some ({| status_code_uint_81 := status_code_uint_81_value |}, bytes)
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

  End ActivateApplicationSystemConfirmedMessage.

  Module LogoutConfirmedMessage.

    (** Logout confirmed message, sent by Taifex to the futures commission merchant. *)
    Record t := {
      status_code_uint_81 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (status_code_uint_81 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (status_code_uint_81 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (status_code_uint_81_value, bytes) =>
          Some ({| status_code_uint_81 := status_code_uint_81_value |}, bytes)
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

  End LogoutConfirmedMessage.

  Module ConfirmConnectionMessage.

    (** Confirm connection message, which either party sends when no new message has arrived from the other after the number of seconds set in the HeartBtInt field of L50. *)
    Record t := {
      status_code_uint_81 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (status_code_uint_81 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (status_code_uint_81 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (status_code_uint_81_value, bytes) =>
          Some ({| status_code_uint_81 := status_code_uint_81_value |}, bytes)
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

  End ConfirmConnectionMessage.

  Module ConnectionConfirmedMessage.

    (** Connection confirmed message, with which a party answers the confirm connection message of the other. *)
    Record t := {
      status_code_uint_81 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (status_code_uint_81 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (status_code_uint_81 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (status_code_uint_81_value, bytes) =>
          Some ({| status_code_uint_81 := status_code_uint_81_value |}, bytes)
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

  End ConnectionConfirmedMessage.

  Module SymbolText.

    (** Text product ID, naming a product by its Ascii character string symbol *)
    Record t := {
      symbol_char_2020 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_char_2020 record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (symbol_char_2020 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (symbol_char_2020_value, bytes) =>
          Some ({| symbol_char_2020 := symbol_char_2020_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolText.

  Module LongSymbolText.

    (** Text product ID in the long product format, naming a product by its Ascii character string symbol *)
    Record t := {
      symbol_char_4040 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_char_4040 record) = 40.

    Definition encode (record : t) : list byte :=
      encode_bytes 40 (symbol_char_4040 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 40 bytes with
      | None => None
      | Some (symbol_char_4040_value, bytes) =>
          Some ({| symbol_char_4040 := symbol_char_4040_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongSymbolText.

  Module ErrorReportMessage.

    (** Error report, with which Taifex rejects an order, quote or inquiry the futures commission merchant sent. *)
    Record t := {
      status_code_uint_81 : N;
      exec_type : list byte;
      fcm_id : N;
      order_no : list byte;
      ord_id : N;
      user_define : list byte;
      rpt_seq : N;
      side : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (status_code_uint_81 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (exec_type record) = 1 /\
      (fcm_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (order_no record) = 5 /\
      (ord_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (user_define record) = 8 /\
      (rpt_seq record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (status_code_uint_81 record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 2 (fcm_id record) ++
      encode_bytes 5 (order_no record) ++
      encode_uint 4 (ord_id record) ++
      encode_bytes 8 (user_define record) ++
      encode_uint 4 (rpt_seq record) ++
      encode_uint 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (status_code_uint_81_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exec_type_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (fcm_id_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (order_no_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ord_id_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (user_define_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (rpt_seq_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      Some ({| status_code_uint_81 := status_code_uint_81_value; exec_type := exec_type_value; fcm_id := fcm_id_value; order_no := order_no_value; ord_id := ord_id_value; user_define := user_define_value; rpt_seq := rpt_seq_value; side := side_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ErrorReportMessage.

  Module SubHdr2.

    (** Tmp Expanded Message Header, which assigns different functionalities to a MessageType by defining additional subcategories for it *)
    Record t := {
      msg_type_ext : N;
      preserve : N;
      msg_time_ns : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_type_ext record < 256 ^ N.of_nat 1)%N /\
      (preserve record < 256 ^ N.of_nat 1)%N /\
      (msg_time_ns record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (msg_type_ext record) ++
      encode_uint 1 (preserve record) ++
      encode_uint 4 (msg_time_ns record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (msg_type_ext_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (preserve_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_time_ns_value, bytes) =>
                  Some ({| msg_type_ext := msg_type_ext_value; preserve := preserve_value; msg_time_ns := msg_time_ns_value |}, bytes)
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

  End SubHdr2.

  Module SymbolNumX.

    (** FLEX Numeric Single Product Serial number, naming a FLEX product by the serial number of the XP08 product and time flow group definition file *)
    Record t := {
      pseq : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (pseq record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (pseq record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (pseq_value, bytes) =>
          Some ({| pseq := pseq_value |}, bytes)
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

  End SymbolNumX.

  Module SymbolTxtX.

    (** FLEX Textual Single Product Symbol, naming a FLEX product by the product symbol of the XP08 product and time flow group definition file *)
    Record t := {
      prod_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (prod_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (prod_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (prod_id_value, bytes) =>
          Some ({| prod_id := prod_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolTxtX.

  Module LegSymSymbolNumX.

    (** FLEX Numeric Single Product Serial number, naming a FLEX product by the serial number of the XP08 product and time flow group definition file *)
    Record t := {
      pseq : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (pseq record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (pseq record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (pseq_value, bytes) =>
          Some ({| pseq := pseq_value |}, bytes)
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

  End LegSymSymbolNumX.

  Module LegSymSymbolTxtX.

    (** FLEX Textual Single Product Symbol, naming a FLEX product by the product symbol of the XP08 product and time flow group definition file *)
    Record t := {
      prod_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (prod_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (prod_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (prod_id_value, bytes) =>
          Some ({| prod_id := prod_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LegSymSymbolTxtX.

  Module SubHdr3.

    (** Tmp Expanded Message Header, which assigns different functionalities to a MessageType by defining additional subcategories for it *)
    Record t := {
      msg_type_ext : N;
      preserve : N;
      msg_time_ns : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_type_ext record < 256 ^ N.of_nat 1)%N /\
      (preserve record < 256 ^ N.of_nat 1)%N /\
      (msg_time_ns record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (msg_type_ext record) ++
      encode_uint 1 (preserve record) ++
      encode_uint 4 (msg_time_ns record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (msg_type_ext_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (preserve_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_time_ns_value, bytes) =>
                  Some ({| msg_type_ext := msg_type_ext_value; preserve := preserve_value; msg_time_ns := msg_time_ns_value |}, bytes)
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

  End SubHdr3.

  Module FlexErrorReportMessage.

    (** FLEX Error Report, with which Taifex rejects a FLEX order, quote or inquiry. *)
    Record t := {
      sub_hdr : SubHdr3.t;
      part_id : N;
      ori_message_type : N;
      status_code_uint_162 : N;
      exec_type : list byte;
      fcm_id : N;
      order_no : list byte;
      ord_id : N;
      user_define : list byte;
      rpt_seq : N;
      side : N;
      reserved_12 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SubHdr3.bounded (sub_hdr record) /\
      (part_id record < 256 ^ N.of_nat 1)%N /\
      (ori_message_type record < 256 ^ N.of_nat 1)%N /\
      (status_code_uint_162 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (exec_type record) = 1 /\
      (fcm_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (order_no record) = 5 /\
      (ord_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (user_define record) = 8 /\
      (rpt_seq record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reserved_12 record) = 12.

    Definition encode (record : t) : list byte :=
      SubHdr3.encode (sub_hdr record) ++
      encode_uint 1 (part_id record) ++
      encode_uint 1 (ori_message_type record) ++
      encode_uint 2 (status_code_uint_162 record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 2 (fcm_id record) ++
      encode_bytes 5 (order_no record) ++
      encode_uint 4 (ord_id record) ++
      encode_bytes 8 (user_define record) ++
      encode_uint 4 (rpt_seq record) ++
      encode_uint 1 (side record) ++
      encode_bytes 12 (reserved_12 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SubHdr3.decode bytes with
      | None => None
      | Some (sub_hdr_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (part_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (ori_message_type_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (status_code_uint_162_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (exec_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (fcm_id_value, bytes) =>
                              match decode_bytes 5 bytes with
                              | None => None
                              | Some (order_no_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (ord_id_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (user_define_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (rpt_seq_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  match decode_bytes 12 bytes with
                                                  | None => None
                                                  | Some (reserved_12_value, bytes) =>
                                                      Some ({| sub_hdr := sub_hdr_value; part_id := part_id_value; ori_message_type := ori_message_type_value; status_code_uint_162 := status_code_uint_162_value; exec_type := exec_type_value; fcm_id := fcm_id_value; order_no := order_no_value; ord_id := ord_id_value; user_define := user_define_value; rpt_seq := rpt_seq_value; side := side_value; reserved_12 := reserved_12_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SubHdr3.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SubHdr3.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SubHdr3.eq_dec]. Defined.

  End FlexErrorReportMessage.

  Module DropCopyInitiateOperationMessage.

    (** TMPDC initiate operation message, with which the broker requests the starting sequence of its drop copies. *)
    Record t := {
      fcm_id : N;
      target_id : N;
      req_cm_seq : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (fcm_id record < 256 ^ N.of_nat 2)%N /\
      (target_id record < 256 ^ N.of_nat 1)%N /\
      (req_cm_seq record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (fcm_id record) ++
      encode_uint 1 (target_id record) ++
      encode_uint 4 (req_cm_seq record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (fcm_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (target_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (req_cm_seq_value, bytes) =>
                  Some ({| fcm_id := fcm_id_value; target_id := target_id_value; req_cm_seq := req_cm_seq_value |}, bytes)
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

  End DropCopyInitiateOperationMessage.

  Module DropCopyInitiateOperationConfirmedMessage.

    (** TMPDC initiate operation confirmed message, with which Taifex answers with a report start notice. *)
    Record t := {
      status_code_uint_81 : N;
      fcm_id : N;
      target_id : N;
      req_cm_seq : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (status_code_uint_81 record < 256 ^ N.of_nat 1)%N /\
      (fcm_id record < 256 ^ N.of_nat 2)%N /\
      (target_id record < 256 ^ N.of_nat 1)%N /\
      (req_cm_seq record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (status_code_uint_81 record) ++
      encode_uint 2 (fcm_id record) ++
      encode_uint 1 (target_id record) ++
      encode_uint 4 (req_cm_seq record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (status_code_uint_81_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (fcm_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (target_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (req_cm_seq_value, bytes) =>
                      Some ({| status_code_uint_81 := status_code_uint_81_value; fcm_id := fcm_id_value; target_id := target_id_value; req_cm_seq := req_cm_seq_value |}, bytes)
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

  End DropCopyInitiateOperationConfirmedMessage.

  Module SubHdr4.

    (** Tmp Expanded Message Header, which assigns different functionalities to a MessageType by defining additional subcategories for it *)
    Record t := {
      msg_type_ext : N;
      preserve : N;
      msg_time_ns : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_type_ext record < 256 ^ N.of_nat 1)%N /\
      (preserve record < 256 ^ N.of_nat 1)%N /\
      (msg_time_ns record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (msg_type_ext record) ++
      encode_uint 1 (preserve record) ++
      encode_uint 4 (msg_time_ns record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (msg_type_ext_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (preserve_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_time_ns_value, bytes) =>
                  Some ({| msg_type_ext := msg_type_ext_value; preserve := preserve_value; msg_time_ns := msg_time_ns_value |}, bytes)
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

  End SubHdr4.

  Module FlexDropCopyInitiateOperationMessage.

    (** TMPDC initiate FLEX operation message, with which the broker subscribes to the FLEX drop copies of a partition. *)
    Record t := {
      sub_hdr : SubHdr4.t;
      part_id : N;
      fcm_id : N;
      target_id : N;
      req_cm_seq : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SubHdr4.bounded (sub_hdr record) /\
      (part_id record < 256 ^ N.of_nat 1)%N /\
      (fcm_id record < 256 ^ N.of_nat 2)%N /\
      (target_id record < 256 ^ N.of_nat 1)%N /\
      (req_cm_seq record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      SubHdr4.encode (sub_hdr record) ++
      encode_uint 1 (part_id record) ++
      encode_uint 2 (fcm_id record) ++
      encode_uint 1 (target_id record) ++
      encode_uint 4 (req_cm_seq record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SubHdr4.decode bytes with
      | None => None
      | Some (sub_hdr_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (part_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (fcm_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (target_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (req_cm_seq_value, bytes) =>
                          Some ({| sub_hdr := sub_hdr_value; part_id := part_id_value; fcm_id := fcm_id_value; target_id := target_id_value; req_cm_seq := req_cm_seq_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SubHdr4.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SubHdr4.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply SubHdr4.eq_dec]. Defined.

  End FlexDropCopyInitiateOperationMessage.

  Module SubHdr5.

    (** Tmp Expanded Message Header, which assigns different functionalities to a MessageType by defining additional subcategories for it *)
    Record t := {
      msg_type_ext : N;
      preserve : N;
      msg_time_ns : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_type_ext record < 256 ^ N.of_nat 1)%N /\
      (preserve record < 256 ^ N.of_nat 1)%N /\
      (msg_time_ns record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (msg_type_ext record) ++
      encode_uint 1 (preserve record) ++
      encode_uint 4 (msg_time_ns record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (msg_type_ext_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (preserve_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_time_ns_value, bytes) =>
                  Some ({| msg_type_ext := msg_type_ext_value; preserve := preserve_value; msg_time_ns := msg_time_ns_value |}, bytes)
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

  End SubHdr5.

  Module FlexDropCopyInitiateOperationConfirmedMessage.

    (** TMPDC initiate FLEX operation confirmed message, with which Taifex confirms the FLEX drop copy subscription. *)
    Record t := {
      sub_hdr : SubHdr5.t;
      part_id : N;
      status_code_uint_162 : N;
      fcm_id : N;
      target_id : N;
      req_cm_seq : N;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SubHdr5.bounded (sub_hdr record) /\
      (part_id record < 256 ^ N.of_nat 1)%N /\
      (status_code_uint_162 record < 256 ^ N.of_nat 2)%N /\
      (fcm_id record < 256 ^ N.of_nat 2)%N /\
      (target_id record < 256 ^ N.of_nat 1)%N /\
      (req_cm_seq record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      SubHdr5.encode (sub_hdr record) ++
      encode_uint 1 (part_id record) ++
      encode_uint 2 (status_code_uint_162 record) ++
      encode_uint 2 (fcm_id record) ++
      encode_uint 1 (target_id record) ++
      encode_uint 4 (req_cm_seq record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SubHdr5.decode bytes with
      | None => None
      | Some (sub_hdr_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (part_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (status_code_uint_162_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (fcm_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (target_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (req_cm_seq_value, bytes) =>
                              match decode_bytes 16 bytes with
                              | None => None
                              | Some (reserved_16_value, bytes) =>
                                  Some ({| sub_hdr := sub_hdr_value; part_id := part_id_value; status_code_uint_162 := status_code_uint_162_value; fcm_id := fcm_id_value; target_id := target_id_value; req_cm_seq := req_cm_seq_value; reserved_16 := reserved_16_value |}, bytes)
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
      rewrite !length_app, !SubHdr5.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SubHdr5.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SubHdr5.eq_dec]. Defined.

  End FlexDropCopyInitiateOperationConfirmedMessage.

  Module MessageTail.

    (** Tmp Message Tail, carrying the check sum of a message *)
    Record t := {
      check_sum : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (check_sum record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (check_sum record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (check_sum_value, bytes) =>
          Some ({| check_sum := check_sum_value |}, bytes)
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

  End MessageTail.

End TaifexDerivativesDropCopyV2187.
