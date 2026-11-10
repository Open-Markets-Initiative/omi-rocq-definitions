From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Shanghai Stock Exchange Market Data Gateway

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
      - a run counted by a field

    License: MIT No Attribution
  *)

Module SseSecuritiesMdgwV063.

  Module StandardHeader.

    Record t := {
      msg_type : list byte;
      sending_time : N;
      msg_seq_num : N;
      body_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (msg_type record) = 4 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 8)%N /\
      (body_length record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (msg_type record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (msg_seq_num record) ++
      encode_uint 4 (body_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (msg_type_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (body_length_value, bytes) =>
                      Some ({| msg_type := msg_type_value; sending_time := sending_time_value; msg_seq_num := msg_seq_num_value; body_length := body_length_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StandardHeader.

  Module LogonMessage.

    (** The client must send this message first when starting a market data session. *)
    Record t := {
      sender_comp_i_d : list byte;
      target_comp_i_d : list byte;
      heart_bt_int : N;
      appl_ver_i_d : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sender_comp_i_d record) = 32 /\
      Datatypes.length (target_comp_i_d record) = 32 /\
      (heart_bt_int record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (appl_ver_i_d record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 32 (sender_comp_i_d record) ++
      encode_bytes 32 (target_comp_i_d record) ++
      encode_uint 2 (heart_bt_int record) ++
      encode_bytes 8 (appl_ver_i_d record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 32 bytes with
      | None => None
      | Some (sender_comp_i_d_value, bytes) =>
          match decode_bytes 32 bytes with
          | None => None
          | Some (target_comp_i_d_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (heart_bt_int_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (appl_ver_i_d_value, bytes) =>
                      Some ({| sender_comp_i_d := sender_comp_i_d_value; target_comp_i_d := target_comp_i_d_value; heart_bt_int := heart_bt_int_value; appl_ver_i_d := appl_ver_i_d_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonMessage.

  Module LogoutMessage.

    (** The logout message starts or confirms the end of a market data session. A disconnection without an exchange of logout messages is treated as an abnormal disconnection. After sending a logout message, neither side of the connection should send any further message. *)
    Record t := {
      session_status : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_status record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (text record) = 256.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_status record) ++
      encode_bytes 256 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_status_value, bytes) =>
          match decode_bytes 256 bytes with
          | None => None
          | Some (text_value, bytes) =>
              Some ({| session_status := session_status_value; text := text_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 260.
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

  Module ChannelHeartbeat.

    (** Tick-by-tick market data supports sending a heartbeat every 3 seconds during idle periods of data sending. If data sending stays busy, the channel heartbeat interval can exceed 3s. *)
    Record t := {
      channel_heartbeat_security_type : N;
      channel_heartbeat_channel_n_o : N;
      appl_last_seq_num : N;
      end_of_channel : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_heartbeat_security_type record < 256 ^ N.of_nat 1)%N /\
      (channel_heartbeat_channel_n_o record < 256 ^ N.of_nat 2)%N /\
      (appl_last_seq_num record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (end_of_channel record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (channel_heartbeat_security_type record) ++
      encode_uint 2 (channel_heartbeat_channel_n_o record) ++
      encode_uint 8 (appl_last_seq_num record) ++
      encode_bytes 1 (end_of_channel record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (channel_heartbeat_security_type_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (channel_heartbeat_channel_n_o_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (appl_last_seq_num_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (end_of_channel_value, bytes) =>
                      Some ({| channel_heartbeat_security_type := channel_heartbeat_security_type_value; channel_heartbeat_channel_n_o := channel_heartbeat_channel_n_o_value; appl_last_seq_num := appl_last_seq_num_value; end_of_channel := end_of_channel_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ChannelHeartbeat.

  Module RetransmissionMessage.

    (** The retransmission message is used to request market data on a channel that supports retransmission. For application messages that can be retransmitted (all types of tick-by-tick market data messages), if application messages are missing, the user can send a retransmission message upstream, which represents a retransmission request. The upstream handles retransmission requests in a "request–reply" manner: it returns the data to be retransmitted according to the start and end sequence numbers specified in the retransmission message, and after the retransmission is complete it returns a retransmission message reporting that the retransmission is complete; if the retransmission fails, it returns a retransmission message reporting that the retransmission failed. The upstream system supports retransmission of only one message gap at a time; when the upstream receives multiple retransmission requests, it returns a retransmission failure for the other request messages. For tick-by-tick market data, the channel code and the message record number can be used to determine whether messages have been lost. When the message record number received is <= the largest message record number already received on this channel, the message has already been received and should be ignored. When the message record number received is > the largest message record number already received +1 (for example, the largest message record number received is 100 and the new message record number is 102), messages have been lost, and the lost data should be recovered by sending a retransmission request. *)
    Record t := {
      retransmission_message_channel_n_o : N;
      resend_type : N;
      appl_beg_seq_num : N;
      appl_end_seq_num : N;
      resend_status : N;
      reject_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (retransmission_message_channel_n_o record < 256 ^ N.of_nat 2)%N /\
      (resend_type record < 256 ^ N.of_nat 1)%N /\
      (appl_beg_seq_num record < 256 ^ N.of_nat 8)%N /\
      (appl_end_seq_num record < 256 ^ N.of_nat 8)%N /\
      (resend_status record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reject_text record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (retransmission_message_channel_n_o record) ++
      encode_uint 1 (resend_type record) ++
      encode_uint 8 (appl_beg_seq_num record) ++
      encode_uint 8 (appl_end_seq_num record) ++
      encode_uint 1 (resend_status record) ++
      encode_bytes 32 (reject_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (retransmission_message_channel_n_o_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (resend_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (appl_beg_seq_num_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (appl_end_seq_num_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (resend_status_value, bytes) =>
                          match decode_bytes 32 bytes with
                          | None => None
                          | Some (reject_text_value, bytes) =>
                              Some ({| retransmission_message_channel_n_o := retransmission_message_channel_n_o_value; resend_type := resend_type_value; appl_beg_seq_num := appl_beg_seq_num_value; appl_end_seq_num := appl_end_seq_num_value; resend_status := resend_status_value; reject_text := reject_text_value |}, bytes)
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

  End RetransmissionMessage.

  Module MarketStatusMessage.

    (** The market status message is used by the exchange to publish information such as the market status and the number of products. It is published periodically and when the market status changes. *)
    Record t := {
      market_status_message_security_type : N;
      trad_ses_mode : N;
      trading_session_i_d : list byte;
      tot_no_related_sym : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_status_message_security_type record < 256 ^ N.of_nat 1)%N /\
      (trad_ses_mode record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trading_session_i_d record) = 8 /\
      (tot_no_related_sym record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (market_status_message_security_type record) ++
      encode_uint 1 (trad_ses_mode record) ++
      encode_bytes 8 (trading_session_i_d record) ++
      encode_uint 4 (tot_no_related_sym record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (market_status_message_security_type_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (trad_ses_mode_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trading_session_i_d_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (tot_no_related_sym_value, bytes) =>
                      Some ({| market_status_message_security_type := market_status_message_security_type_value; trad_ses_mode := trad_ses_mode_value; trading_session_i_d := trading_session_i_d_value; tot_no_related_sym := tot_no_related_sym_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketStatusMessage.

  Module Tick_by_TickOrderMarketDataExtensionFields.

    Record t := {
      side : list byte;
      quote_i_d : list byte;
      member_i_d : list byte;
      trader_code : list byte;
      full_amount_trade : N;
      settl_type : N;
      contract_multiplier : N;
      expiration_days : N;
      tick_by_tick_order_market_data_extension_fields_total_value_traded : N;
      basket_i_d : list byte;
      investor_name : list byte;
      bid_trans_type : N;
      bid_exec_inst_type : N;
      expire_date : N;
      secondary_order_i_d : list byte;
      min_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (side record) = 1 /\
      Datatypes.length (quote_i_d record) = 18 /\
      Datatypes.length (member_i_d record) = 12 /\
      Datatypes.length (trader_code record) = 12 /\
      (full_amount_trade record < 256 ^ N.of_nat 1)%N /\
      (settl_type record < 256 ^ N.of_nat 1)%N /\
      (contract_multiplier record < 256 ^ N.of_nat 4)%N /\
      (expiration_days record < 256 ^ N.of_nat 2)%N /\
      (tick_by_tick_order_market_data_extension_fields_total_value_traded record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (basket_i_d record) = 16 /\
      Datatypes.length (investor_name record) = 32 /\
      (bid_trans_type record < 256 ^ N.of_nat 1)%N /\
      (bid_exec_inst_type record < 256 ^ N.of_nat 1)%N /\
      (expire_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (secondary_order_i_d record) = 18 /\
      (min_qty record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (side record) ++
      encode_bytes 18 (quote_i_d record) ++
      encode_bytes 12 (member_i_d record) ++
      encode_bytes 12 (trader_code record) ++
      encode_uint 1 (full_amount_trade record) ++
      encode_uint 1 (settl_type record) ++
      encode_uint 4 (contract_multiplier record) ++
      encode_uint 2 (expiration_days record) ++
      encode_uint 8 (tick_by_tick_order_market_data_extension_fields_total_value_traded record) ++
      encode_bytes 16 (basket_i_d record) ++
      encode_bytes 32 (investor_name record) ++
      encode_uint 1 (bid_trans_type record) ++
      encode_uint 1 (bid_exec_inst_type record) ++
      encode_uint 4 (expire_date record) ++
      encode_bytes 18 (secondary_order_i_d record) ++
      encode_uint 8 (min_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (side_value, bytes) =>
          match decode_bytes 18 bytes with
          | None => None
          | Some (quote_i_d_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (member_i_d_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (trader_code_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (full_amount_trade_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (settl_type_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (contract_multiplier_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (expiration_days_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (tick_by_tick_order_market_data_extension_fields_total_value_traded_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (basket_i_d_value, bytes) =>
                                              match decode_bytes 32 bytes with
                                              | None => None
                                              | Some (investor_name_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (bid_trans_type_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (bid_exec_inst_type_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (expire_date_value, bytes) =>
                                                              match decode_bytes 18 bytes with
                                                              | None => None
                                                              | Some (secondary_order_i_d_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (min_qty_value, bytes) =>
                                                                      Some ({| side := side_value; quote_i_d := quote_i_d_value; member_i_d := member_i_d_value; trader_code := trader_code_value; full_amount_trade := full_amount_trade_value; settl_type := settl_type_value; contract_multiplier := contract_multiplier_value; expiration_days := expiration_days_value; tick_by_tick_order_market_data_extension_fields_total_value_traded := tick_by_tick_order_market_data_extension_fields_total_value_traded_value; basket_i_d := basket_i_d_value; investor_name := investor_name_value; bid_trans_type := bid_trans_type_value; bid_exec_inst_type := bid_exec_inst_type_value; expire_date := expire_date_value; secondary_order_i_d := secondary_order_i_d_value; min_qty := min_qty_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 139.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Tick_by_TickOrderMarketDataExtensionFields.

  Module Tick_by_TickTradeMarketDataExtensionFields.

    Record t := {
      bid_appl_seq_num : list byte;
      offer_appl_seq_num : list byte;
      tick_by_tick_trade_market_data_extension_fields_total_value_traded : N;
      trade_method : N;
      margin_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_appl_seq_num record) = 18 /\
      Datatypes.length (offer_appl_seq_num record) = 18 /\
      (tick_by_tick_trade_market_data_extension_fields_total_value_traded record < 256 ^ N.of_nat 8)%N /\
      (trade_method record < 256 ^ N.of_nat 1)%N /\
      (margin_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 18 (bid_appl_seq_num record) ++
      encode_bytes 18 (offer_appl_seq_num record) ++
      encode_uint 8 (tick_by_tick_trade_market_data_extension_fields_total_value_traded record) ++
      encode_uint 1 (trade_method record) ++
      encode_uint 8 (margin_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 18 bytes with
      | None => None
      | Some (bid_appl_seq_num_value, bytes) =>
          match decode_bytes 18 bytes with
          | None => None
          | Some (offer_appl_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (tick_by_tick_trade_market_data_extension_fields_total_value_traded_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (trade_method_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (margin_price_value, bytes) =>
                          Some ({| bid_appl_seq_num := bid_appl_seq_num_value; offer_appl_seq_num := offer_appl_seq_num_value; tick_by_tick_trade_market_data_extension_fields_total_value_traded := tick_by_tick_trade_market_data_extension_fields_total_value_traded_value; trade_method := trade_method_value; margin_price := margin_price_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 53.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Tick_by_TickTradeMarketDataExtensionFields.

  Module StandardTrailer.

    (** The checksum is calculated from the start of the message header (header included) to the end of the message body. See Appendix 1 "Calculating the checksum" for sample code. *)
    Record t := {
      check_sum : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (check_sum record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (check_sum record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (check_sum_value, bytes) =>
          Some ({| check_sum := check_sum_value |}, bytes)
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

  End StandardTrailer.

End SseSecuritiesMdgwV063.
