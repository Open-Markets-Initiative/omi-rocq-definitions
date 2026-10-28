From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Stock Exchange of India Ltd Order Entry

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
      - a Composite rule
      - a field read in bits
  *)

Module NseCmOrderEntryV66Client.

  Module MessageHeader.

    (** MESSAGE_HEADER *)
    Record t := {
      transaction_code : N;
      log_time : N;
      alpha_char : list byte;
      trader_id : N;
      error_code : N;
      header_timestamp : N;
      time_stamp_1 : list byte;
      time_stamp_2 : list byte;
      message_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_code record < 256 ^ N.of_nat 2)%N /\
      (log_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (alpha_char record) = 2 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      (error_code record < 256 ^ N.of_nat 2)%N /\
      (header_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (time_stamp_1 record) = 8 /\
      Datatypes.length (time_stamp_2 record) = 8 /\
      (message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (transaction_code record) ++
      encode_uint 4 (log_time record) ++
      encode_bytes 2 (alpha_char record) ++
      encode_uint 4 (trader_id record) ++
      encode_uint 2 (error_code record) ++
      encode_uint 8 (header_timestamp record) ++
      encode_bytes 8 (time_stamp_1 record) ++
      encode_bytes 8 (time_stamp_2 record) ++
      encode_uint 2 (message_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (transaction_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (log_time_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (alpha_char_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (error_code_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (header_timestamp_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (time_stamp_1_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (time_stamp_2_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (message_length_value, bytes) =>
                                          Some ({| transaction_code := transaction_code_value; log_time := log_time_value; alpha_char := alpha_char_value; trader_id := trader_id_value; error_code := error_code_value; header_timestamp := header_timestamp_value; time_stamp_1 := time_stamp_1_value; time_stamp_2 := time_stamp_2_value; message_length := message_length_value |}, bytes)
                                      end
                                  end
                              end
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module CancelOnLogoutStatusRequestMessage.

    (** Sent as COL_USER_STATUS_CHANGE _IN *)
    Record t := {
      user_id : N;
      colo_user_bit : list byte;
      reserved_7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (colo_user_bit record) = 1 /\
      (reserved_7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 1 (colo_user_bit record) ++
      encode_uint 7 (reserved_7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (colo_user_bit_value, bytes) =>
              match decode_uint 7 bytes with
              | None => None
              | Some (reserved_7_value, bytes) =>
                  Some ({| user_id := user_id_value; colo_user_bit := colo_user_bit_value; reserved_7 := reserved_7_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End CancelOnLogoutStatusRequestMessage.

  Module SecInfo.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End SecInfo.

  Module AuctionInquiryRequestMessage.

    (** Sent as AUCTION_INQUIRY_IN *)
    Record t := {
      sec_info : SecInfo.t;
      auction_no : N;
      page_indicator : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SecInfo.bounded (sec_info record) /\
      (auction_no record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (page_indicator record) = 1 /\
      Datatypes.length (filler record) = 1.

    Definition encode (record : t) : list byte :=
      SecInfo.encode (sec_info record) ++
      encode_uint 2 (auction_no record) ++
      encode_bytes 1 (page_indicator record) ++
      encode_bytes 1 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SecInfo.decode bytes with
      | None => None
      | Some (sec_info_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (auction_no_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (page_indicator_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (filler_value, bytes) =>
                      Some ({| sec_info := sec_info_value; auction_no := auction_no_value; page_indicator := page_indicator_value; filler := filler_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SecInfo.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SecInfo.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SecInfo.eq_dec]. Defined.

  End AuctionInquiryRequestMessage.

  Module BoxSignOffMessage.

    (** Sent as BOX_SIGN_OFF *)
    Record t := {
      box_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (box_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (box_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (box_id_value, bytes) =>
          Some ({| box_id := box_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End BoxSignOffMessage.

  Module BoxSignOnRequestMessage.

    (** Sent as BOX_SIGN_ON_REQUEST_IN *)
    Record t := {
      box_id : N;
      broker_id : list byte;
      reserved_5 : N;
      session_key : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (box_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (broker_id record) = 5 /\
      (reserved_5 record < 256 ^ N.of_nat 5)%N /\
      Datatypes.length (session_key record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (box_id record) ++
      encode_bytes 5 (broker_id record) ++
      encode_uint 5 (reserved_5 record) ++
      encode_bytes 8 (session_key record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (box_id_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (broker_id_value, bytes) =>
              match decode_uint 5 bytes with
              | None => None
              | Some (reserved_5_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (session_key_value, bytes) =>
                      Some ({| box_id := box_id_value; broker_id := broker_id_value; reserved_5 := reserved_5_value; session_key := session_key_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BoxSignOnRequestMessage.

  Module GatewayRouterRequestMessage.

    (** Sent as GR_REQUEST *)
    Record t := {
      box_id : N;
      broker_id : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (box_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (broker_id record) = 5 /\
      Datatypes.length (filler record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (box_id record) ++
      encode_bytes 5 (broker_id record) ++
      encode_bytes 1 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (box_id_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (broker_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (filler_value, bytes) =>
                  Some ({| box_id := box_id_value; broker_id := broker_id_value; filler := filler_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GatewayRouterRequestMessage.

  Module SecInfo2.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End SecInfo2.

  Module PasswordResetInMessage.

    (** Sent as RESET_PASSWORD_IN *)
    Record t := {
      user_id : N;
      reserved_14 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_14 record) = 14.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 14 (reserved_14 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (reserved_14_value, bytes) =>
              Some ({| user_id := user_id_value; reserved_14 := reserved_14_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PasswordResetInMessage.

  Module SecInfo3.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End SecInfo3.

  Module TradeInquiryInMessage.

    (** Sent as TRADE_CANCEL_IN, TRADE_MOD_IN *)
    Record t := {
      sec_info : SecInfo3.t;
      fill_number : N;
      fill_qty : N;
      fill_price : N;
      market_type : N;
      new_volume : N;
      reserved_24 : list byte;
      buy_broker_id : list byte;
      sell_broker_id : list byte;
      trader_id : N;
      requested_by : N;
      buy_account_number : list byte;
      sell_account_number : list byte;
      buy_pan : list byte;
      sell_pan : list byte;
      reserved_60 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SecInfo3.bounded (sec_info record) /\
      (fill_number record < 256 ^ N.of_nat 4)%N /\
      (fill_qty record < 256 ^ N.of_nat 4)%N /\
      (fill_price record < 256 ^ N.of_nat 4)%N /\
      (market_type record < 256 ^ N.of_nat 2)%N /\
      (new_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_24 record) = 24 /\
      Datatypes.length (buy_broker_id record) = 5 /\
      Datatypes.length (sell_broker_id record) = 5 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      (requested_by record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (buy_account_number record) = 10 /\
      Datatypes.length (sell_account_number record) = 10 /\
      Datatypes.length (buy_pan record) = 10 /\
      Datatypes.length (sell_pan record) = 10 /\
      Datatypes.length (reserved_60 record) = 60.

    Definition encode (record : t) : list byte :=
      SecInfo3.encode (sec_info record) ++
      encode_uint 4 (fill_number record) ++
      encode_uint 4 (fill_qty record) ++
      encode_uint 4 (fill_price record) ++
      encode_uint 2 (market_type record) ++
      encode_uint 4 (new_volume record) ++
      encode_bytes 24 (reserved_24 record) ++
      encode_bytes 5 (buy_broker_id record) ++
      encode_bytes 5 (sell_broker_id record) ++
      encode_uint 4 (trader_id record) ++
      encode_uint 2 (requested_by record) ++
      encode_bytes 10 (buy_account_number record) ++
      encode_bytes 10 (sell_account_number record) ++
      encode_bytes 10 (buy_pan record) ++
      encode_bytes 10 (sell_pan record) ++
      encode_bytes 60 (reserved_60 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SecInfo3.decode bytes with
      | None => None
      | Some (sec_info_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (fill_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (fill_qty_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (fill_price_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (market_type_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (new_volume_value, bytes) =>
                              match decode_bytes 24 bytes with
                              | None => None
                              | Some (reserved_24_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (buy_broker_id_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (sell_broker_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (trader_id_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (requested_by_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (buy_account_number_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (sell_account_number_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (buy_pan_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (sell_pan_value, bytes) =>
                                                                  match decode_bytes 60 bytes with
                                                                  | None => None
                                                                  | Some (reserved_60_value, bytes) =>
                                                                      Some ({| sec_info := sec_info_value; fill_number := fill_number_value; fill_qty := fill_qty_value; fill_price := fill_price_value; market_type := market_type_value; new_volume := new_volume_value; reserved_24 := reserved_24_value; buy_broker_id := buy_broker_id_value; sell_broker_id := sell_broker_id_value; trader_id := trader_id_value; requested_by := requested_by_value; buy_account_number := buy_account_number_value; sell_account_number := sell_account_number_value; buy_pan := buy_pan_value; sell_pan := sell_pan_value; reserved_60 := reserved_60_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 170.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SecInfo3.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SecInfo3.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SecInfo3.eq_dec]. Defined.

  End TradeInquiryInMessage.

  Module UpdateLocalDatabaseRequestMessage.

    (** Sent as UPDATE_LOCALDB_IN *)
    Record t := {
      last_update_security_time : N;
      last_update_participant_time : N;
      request_for_open_orders : list byte;
      reserved_1 : N;
      normal_market_status : N;
      odd_lot_market_status : N;
      spot_market_status : N;
      auction_market_status : N;
      call_auction_1_market_status : N;
      call_auction_2_market_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_security_time record < 256 ^ N.of_nat 4)%N /\
      (last_update_participant_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (request_for_open_orders record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (normal_market_status record < 256 ^ N.of_nat 2)%N /\
      (odd_lot_market_status record < 256 ^ N.of_nat 2)%N /\
      (spot_market_status record < 256 ^ N.of_nat 2)%N /\
      (auction_market_status record < 256 ^ N.of_nat 2)%N /\
      (call_auction_1_market_status record < 256 ^ N.of_nat 2)%N /\
      (call_auction_2_market_status record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_update_security_time record) ++
      encode_uint 4 (last_update_participant_time record) ++
      encode_bytes 1 (request_for_open_orders record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (normal_market_status record) ++
      encode_uint 2 (odd_lot_market_status record) ++
      encode_uint 2 (spot_market_status record) ++
      encode_uint 2 (auction_market_status record) ++
      encode_uint 2 (call_auction_1_market_status record) ++
      encode_uint 2 (call_auction_2_market_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_update_security_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (last_update_participant_time_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (request_for_open_orders_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (normal_market_status_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (odd_lot_market_status_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (spot_market_status_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (auction_market_status_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (call_auction_1_market_status_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (call_auction_2_market_status_value, bytes) =>
                                              Some ({| last_update_security_time := last_update_security_time_value; last_update_participant_time := last_update_participant_time_value; request_for_open_orders := request_for_open_orders_value; reserved_1 := reserved_1_value; normal_market_status := normal_market_status_value; odd_lot_market_status := odd_lot_market_status_value; spot_market_status := spot_market_status_value; auction_market_status := auction_market_status_value; call_auction_1_market_status := call_auction_1_market_status_value; call_auction_2_market_status := call_auction_2_market_status_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UpdateLocalDatabaseRequestMessage.

  Module TradeModificationCancellationStatusRequestMessage.

    (** Sent as TRD_MOD_CXL_STATUS_CHANGE _IN *)
    Record t := {
      user_id : N;
      trd_mod_cxl_bit : list byte;
      reserved_7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trd_mod_cxl_bit record) = 1 /\
      (reserved_7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 1 (trd_mod_cxl_bit record) ++
      encode_uint 7 (reserved_7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trd_mod_cxl_bit_value, bytes) =>
              match decode_uint 7 bytes with
              | None => None
              | Some (reserved_7_value, bytes) =>
                  Some ({| user_id := user_id_value; trd_mod_cxl_bit := trd_mod_cxl_bit_value; reserved_7 := reserved_7_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End TradeModificationCancellationStatusRequestMessage.

  Module UserUnlockRequestMessage.

    (** Sent as USER_ADDR_UNLOCK_IN *)
    Record t := {
      user_id : N;
      reserved_24 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_24 record) = 24.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 24 (reserved_24 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 24 bytes with
          | None => None
          | Some (reserved_24_value, bytes) =>
              Some ({| user_id := user_id_value; reserved_24 := reserved_24_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UserUnlockRequestMessage.

End NseCmOrderEntryV66Client.
