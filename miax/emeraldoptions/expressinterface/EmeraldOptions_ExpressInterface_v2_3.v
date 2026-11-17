From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings Express Interface

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
      - a length prefix framing what follows
      - a run counted by a field

    License: MIT No Attribution
  *)

Module EmeraldOptionsExpressInterfaceV23.

  Module SesmPacketHeader.

    (** SesM packet header *)
    Record t := {
      sesm_packet_length : N;
      sesm_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sesm_packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sesm_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (sesm_packet_length record) ++
      encode_bytes 1 (sesm_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (sesm_packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sesm_packet_type_value, bytes) =>
              Some ({| sesm_packet_length := sesm_packet_length_value; sesm_packet_type := sesm_packet_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SesmPacketHeader.

  Module SimpleSeriesUpdate.

    (** This is the message format that will be used to disseminate all Option series traded on MIAX for the current session on the cloud associated for this connection. *)
    Record t := {
      product_add_update_time : N;
      product_id : N;
      underlying_symbol : list byte;
      security_symbol : list byte;
      expiration_date : list byte;
      strike_price : N;
      call_or_put : list byte;
      opening_time : list byte;
      closing_time : list byte;
      restricted_option : list byte;
      long_term_option : list byte;
      active_on_emerald : list byte;
      emerald_bbo_posting_increment_indicator : list byte;
      quote_acceptance_increment_indicator : list byte;
      opening_underlying_market_code : list byte;
      priority_quote_width : N;
      reserved_8 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (product_add_update_time record < 256 ^ N.of_nat 8)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (security_symbol record) = 6 /\
      Datatypes.length (expiration_date record) = 8 /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (call_or_put record) = 1 /\
      Datatypes.length (opening_time record) = 8 /\
      Datatypes.length (closing_time record) = 8 /\
      Datatypes.length (restricted_option record) = 1 /\
      Datatypes.length (long_term_option record) = 1 /\
      Datatypes.length (active_on_emerald record) = 1 /\
      Datatypes.length (emerald_bbo_posting_increment_indicator record) = 1 /\
      Datatypes.length (quote_acceptance_increment_indicator record) = 1 /\
      Datatypes.length (opening_underlying_market_code record) = 1 /\
      (priority_quote_width record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_8 record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (product_add_update_time record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 6 (security_symbol record) ++
      encode_bytes 8 (expiration_date record) ++
      encode_uint_le 4 (strike_price record) ++
      encode_bytes 1 (call_or_put record) ++
      encode_bytes 8 (opening_time record) ++
      encode_bytes 8 (closing_time record) ++
      encode_bytes 1 (restricted_option record) ++
      encode_bytes 1 (long_term_option record) ++
      encode_bytes 1 (active_on_emerald record) ++
      encode_bytes 1 (emerald_bbo_posting_increment_indicator record) ++
      encode_bytes 1 (quote_acceptance_increment_indicator record) ++
      encode_bytes 1 (opening_underlying_market_code record) ++
      encode_uint_le 4 (priority_quote_width record) ++
      encode_bytes 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (product_add_update_time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (security_symbol_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (expiration_date_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (call_or_put_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (opening_time_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (closing_time_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (restricted_option_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (long_term_option_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (active_on_emerald_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (emerald_bbo_posting_increment_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (quote_acceptance_increment_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (opening_underlying_market_code_value, bytes) =>
                                                                  match decode_uint_le 4 bytes with
                                                                  | None => None
                                                                  | Some (priority_quote_width_value, bytes) =>
                                                                      match decode_bytes 8 bytes with
                                                                      | None => None
                                                                      | Some (reserved_8_value, bytes) =>
                                                                          Some ({| product_add_update_time := product_add_update_time_value; product_id := product_id_value; underlying_symbol := underlying_symbol_value; security_symbol := security_symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; call_or_put := call_or_put_value; opening_time := opening_time_value; closing_time := closing_time_value; restricted_option := restricted_option_value; long_term_option := long_term_option_value; active_on_emerald := active_on_emerald_value; emerald_bbo_posting_increment_indicator := emerald_bbo_posting_increment_indicator_value; quote_acceptance_increment_indicator := quote_acceptance_increment_indicator_value; opening_underlying_market_code := opening_underlying_market_code_value; priority_quote_width := priority_quote_width_value; reserved_8 := reserved_8_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleSeriesUpdate.

  Module ValidQuoteWidthForOpening.

    (** This message format will be used to convey to the firms the Valid Quote Width settings applicable to the Opening process of Emerald Options market. Each message describes a row of the Valid Quote Width table with a low end of the applicable price range and corresponding maximum quote width. The high end of the applicable price range is up to, but not including the next row’s low end applicable price range if provided or infinity for the last row. If the table has to be reloaded, all rows will be resent. Refer to Appendix C: Messaging for Valid Quote Width for Opening for an example. *)
    Record t := {
      notification_time : N;
      mpv_class : list byte;
      low_end_of_applicable_range : N;
      maximum_quote_width : N;
      long_term_option_multiplier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpv_class record) = 1 /\
      (low_end_of_applicable_range record < 256 ^ N.of_nat 4)%N /\
      (maximum_quote_width record < 256 ^ N.of_nat 4)%N /\
      (long_term_option_multiplier record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 1 (mpv_class record) ++
      encode_uint_le 4 (low_end_of_applicable_range record) ++
      encode_uint_le 4 (maximum_quote_width record) ++
      encode_uint_le 4 (long_term_option_multiplier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (mpv_class_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (low_end_of_applicable_range_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (maximum_quote_width_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (long_term_option_multiplier_value, bytes) =>
                          Some ({| notification_time := notification_time_value; mpv_class := mpv_class_value; low_end_of_applicable_range := low_end_of_applicable_range_value; maximum_quote_width := maximum_quote_width_value; long_term_option_multiplier := long_term_option_multiplier_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ValidQuoteWidthForOpening.

  Module SimpleEnhancedQuoteEQuoteResponse.

    (** This message indicates if the eQuote was accepted or rejected. Note that this message does not report executions. For executions, please refer to the Execution notification. For the unexecuted part that gets canceled, please refer to the Cancel notification. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      e_quote_id : N;
      e_quote_request_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      (e_quote_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (e_quote_request_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 8 (e_quote_id record) ++
      encode_bytes 1 (e_quote_request_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (e_quote_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (e_quote_request_status_value, bytes) =>
                      Some ({| client_message_id := client_message_id_value; mpid := mpid_value; e_quote_id := e_quote_id_value; e_quote_request_status := e_quote_request_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleEnhancedQuoteEQuoteResponse.

  Module ComplexEnhancedQuoteEQuoteResponse.

    (** This message indicates if the complex eQuote was accepted or rejected. Note that this message does not report executions. For executions, please refer to the Execution notification. For the handling of any unexecuted portion that was canceled, please refer to the Cancel notification. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      e_quote_id : N;
      e_quote_request_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      (e_quote_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (e_quote_request_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 8 (e_quote_id record) ++
      encode_bytes 1 (e_quote_request_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (e_quote_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (e_quote_request_status_value, bytes) =>
                      Some ({| client_message_id := client_message_id_value; mpid := mpid_value; e_quote_id := e_quote_id_value; e_quote_request_status := e_quote_request_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexEnhancedQuoteEQuoteResponse.

  Module SystemStateNotification.

    (** This message format is used to notify the firms of the state changes of the system. This is an exchange-wide notification and not a symbol or member based notification. *)
    Record t := {
      notification_time : N;
      mei_version : list byte;
      session_id : N;
      system_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mei_version record) = 8 /\
      (session_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (system_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 8 (mei_version record) ++
      encode_uint 1 (session_id record) ++
      encode_bytes 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (mei_version_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      Some ({| notification_time := notification_time_value; mei_version := mei_version_value; session_id := session_id_value; system_status := system_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemStateNotification.

  Module ProductTradingStatusNotification.

    (** This message format will be used to notify the firms of changes to the trading status of an option. *)
    Record t := {
      notification_time : N;
      product_id : N;
      trading_status : list byte;
      expected_event_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_status record) = 1 /\
      (expected_event_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 1 (trading_status record) ++
      encode_uint_le 8 (expected_event_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_status_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (expected_event_time_value, bytes) =>
                      Some ({| notification_time := notification_time_value; product_id := product_id_value; trading_status := trading_status_value; expected_event_time := expected_event_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ProductTradingStatusNotification.

  Module UnderlyingTradingStatusNotification.

    (** This message format will be used to notify the firms of changes to the trading status of all the options of an underlying. *)
    Record t := {
      notification_time : N;
      underlying_symbol : list byte;
      trading_status : list byte;
      event_reason : list byte;
      expected_event_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (event_reason record) = 1 /\
      (expected_event_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 1 (event_reason record) ++
      encode_uint_le 8 (expected_event_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (underlying_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_status_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (event_reason_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (expected_event_time_value, bytes) =>
                          Some ({| notification_time := notification_time_value; underlying_symbol := underlying_symbol_value; trading_status := trading_status_value; event_reason := event_reason_value; expected_event_time := expected_event_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingTradingStatusNotification.

  Module QuoteWidthReliefNotification.

    (** This message format will be used to notify the firms if and when Emerald grants relief to the valid quote width parameters for Opening as specified in the rules and regulatory circulars of MIAX Options market. *)
    Record t := {
      notification_time : N;
      underlying_symbol : list byte;
      relief_multiplier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      (relief_multiplier record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_uint_le 4 (relief_multiplier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (underlying_symbol_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (relief_multiplier_value, bytes) =>
                  Some ({| notification_time := notification_time_value; underlying_symbol := underlying_symbol_value; relief_multiplier := relief_multiplier_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteWidthReliefNotification.

  Module SimpleArmProtectionSettingsNotification.

    (** This message format will be used to notify firms of their ARM settings. All the ARM settings will be published upon system initialization and each subsequent change will also be published. *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      underlying_symbol : list byte;
      allowable_engagement_percentage : N;
      counting_period : N;
      action : list byte;
      source : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      (allowable_engagement_percentage record < 256 ^ N.of_nat 4)%N /\
      (counting_period record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (action record) = 1 /\
      Datatypes.length (source record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_uint_le 4 (allowable_engagement_percentage record) ++
      encode_uint_le 2 (counting_period record) ++
      encode_bytes 1 (action record) ++
      encode_bytes 1 (source record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (allowable_engagement_percentage_value, bytes) =>
                      match decode_uint_le 2 bytes with
                      | None => None
                      | Some (counting_period_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (action_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (source_value, bytes) =>
                                  Some ({| notification_time := notification_time_value; mpid := mpid_value; underlying_symbol := underlying_symbol_value; allowable_engagement_percentage := allowable_engagement_percentage_value; counting_period := counting_period_value; action := action_value; source := source_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleArmProtectionSettingsNotification.

  Module Arm2UnderlyingLevelProtectionSettingsNotification.

    (** This message format will be used to notify firms of their ARM2 Underlying Level protection settings. *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      action : list byte;
      underlying_symbol : list byte;
      arm_threshold_count : N;
      arm_2_counting_period : N;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (action record) = 1 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      (arm_threshold_count record < 256 ^ N.of_nat 4)%N /\
      (arm_2_counting_period record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (action record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_uint_le 4 (arm_threshold_count record) ++
      encode_uint_le 4 (arm_2_counting_period record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (action_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (underlying_symbol_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (arm_threshold_count_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (arm_2_counting_period_value, bytes) =>
                              match decode_bytes 16 bytes with
                              | None => None
                              | Some (reserved_16_value, bytes) =>
                                  Some ({| notification_time := notification_time_value; mpid := mpid_value; action := action_value; underlying_symbol := underlying_symbol_value; arm_threshold_count := arm_threshold_count_value; arm_2_counting_period := arm_2_counting_period_value; reserved_16 := reserved_16_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Arm2UnderlyingLevelProtectionSettingsNotification.

  Module SingleSideLiquidityProtectionTriggerNotification.

    (** This message format will be used to notify firms when a Single Side Liquidity Protection is triggered for a Emerald Option or Complex Strategy. *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      security_id_scope : list byte;
      security_id : N;
      side : list byte;
      triggering_client_message_id : N;
      triggering_bulk_quote_index : N;
      reserved_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (security_id_scope record) = 1 /\
      (security_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (triggering_client_message_id record < 256 ^ N.of_nat 4)%N /\
      (triggering_bulk_quote_index record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reserved_4 record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (security_id_scope record) ++
      encode_uint_le 4 (security_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint_le 4 (triggering_client_message_id record) ++
      encode_uint 1 (triggering_bulk_quote_index record) ++
      encode_bytes 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_id_scope_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (security_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (triggering_client_message_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (triggering_bulk_quote_index_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (reserved_4_value, bytes) =>
                                      Some ({| notification_time := notification_time_value; mpid := mpid_value; security_id_scope := security_id_scope_value; security_id := security_id_value; side := side_value; triggering_client_message_id := triggering_client_message_id_value; triggering_bulk_quote_index := triggering_bulk_quote_index_value; reserved_4 := reserved_4_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideLiquidityProtectionTriggerNotification.

  Module Arm2UnderlyingLevelProtectionNotification.

    (** This message format will be used to notify firms about ARM2 Underlying Level protection events. *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      underlying_symbol : list byte;
      notification_type : list byte;
      arm_threshold_count : N;
      arm_2_counting_period : N;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (notification_type record) = 1 /\
      (arm_threshold_count record < 256 ^ N.of_nat 4)%N /\
      (arm_2_counting_period record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (notification_type record) ++
      encode_uint_le 4 (arm_threshold_count record) ++
      encode_uint_le 4 (arm_2_counting_period record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (notification_type_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (arm_threshold_count_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (arm_2_counting_period_value, bytes) =>
                              match decode_bytes 16 bytes with
                              | None => None
                              | Some (reserved_16_value, bytes) =>
                                  Some ({| notification_time := notification_time_value; mpid := mpid_value; underlying_symbol := underlying_symbol_value; notification_type := notification_type_value; arm_threshold_count := arm_threshold_count_value; arm_2_counting_period := arm_2_counting_period_value; reserved_16 := reserved_16_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Arm2UnderlyingLevelProtectionNotification.

  Module Arm2FirmLevelProtectionNotification.

    (** This message format will be used to notify firms about ARM2 Firm Level protection events. *)
    Record t := {
      notification_time : N;
      arm_threshold_count : N;
      arm_2_counting_period : N;
      notification_type : list byte;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      (arm_threshold_count record < 256 ^ N.of_nat 4)%N /\
      (arm_2_counting_period record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (notification_type record) = 1 /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_uint_le 4 (arm_threshold_count record) ++
      encode_uint_le 4 (arm_2_counting_period record) ++
      encode_bytes 1 (notification_type record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (arm_threshold_count_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (arm_2_counting_period_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (notification_type_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (reserved_16_value, bytes) =>
                          Some ({| notification_time := notification_time_value; arm_threshold_count := arm_threshold_count_value; arm_2_counting_period := arm_2_counting_period_value; notification_type := notification_type_value; reserved_16 := reserved_16_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Arm2FirmLevelProtectionNotification.

  Module CancelNotification.

    (** This is the message format that will be used to notify firms about system generated or firm requested simple quote and simple or complex eQuote cancels. *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      product_id_or_strategy_id : N;
      liquidity_type : list byte;
      client_message_id : N;
      bulk_quote_index : N;
      quotee_quote_side : list byte;
      size : N;
      engine_sequence_number : N;
      cancel_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      (product_id_or_strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (liquidity_type record) = 1 /\
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      (bulk_quote_index record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (quotee_quote_side record) = 1 /\
      (size record < 256 ^ N.of_nat 4)%N /\
      (engine_sequence_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cancel_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 4 (product_id_or_strategy_id record) ++
      encode_bytes 1 (liquidity_type record) ++
      encode_uint_le 4 (client_message_id record) ++
      encode_uint 1 (bulk_quote_index record) ++
      encode_bytes 1 (quotee_quote_side record) ++
      encode_uint_le 4 (size record) ++
      encode_uint_le 8 (engine_sequence_number record) ++
      encode_bytes 1 (cancel_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (product_id_or_strategy_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (liquidity_type_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_message_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (bulk_quote_index_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (quotee_quote_side_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (size_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (engine_sequence_number_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (cancel_reason_value, bytes) =>
                                              Some ({| notification_time := notification_time_value; mpid := mpid_value; product_id_or_strategy_id := product_id_or_strategy_id_value; liquidity_type := liquidity_type_value; client_message_id := client_message_id_value; bulk_quote_index := bulk_quote_index_value; quotee_quote_side := quotee_quote_side_value; size := size_value; engine_sequence_number := engine_sequence_number_value; cancel_reason := cancel_reason_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelNotification.

  Module OptionExecutionNotification.

    (** This message format will be used to notify the firms of executions of their simple quotes and simple or complex eQuotes. *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      product_id : N;
      liquidity_type : list byte;
      client_message_id : N;
      bulk_quote_index : N;
      event_id : N;
      trade_id : N;
      execution_id : N;
      reserved_1 : list byte;
      trade_status : list byte;
      last_price : N;
      side : list byte;
      last_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (liquidity_type record) = 1 /\
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      (bulk_quote_index record < 256 ^ N.of_nat 1)%N /\
      (event_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (trade_status record) = 1 /\
      (last_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (last_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 1 (liquidity_type record) ++
      encode_uint_le 4 (client_message_id record) ++
      encode_uint 1 (bulk_quote_index record) ++
      encode_uint_le 4 (event_id record) ++
      encode_uint_le 4 (trade_id record) ++
      encode_uint_le 8 (execution_id record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (trade_status record) ++
      encode_uint_le 4 (last_price record) ++
      encode_bytes 1 (side record) ++
      encode_uint_le 4 (last_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (liquidity_type_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_message_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (bulk_quote_index_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (event_id_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (trade_id_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (execution_id_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (reserved_1_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (trade_status_value, bytes) =>
                                                  match decode_uint_le 4 bytes with
                                                  | None => None
                                                  | Some (last_price_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_uint_le 4 bytes with
                                                          | None => None
                                                          | Some (last_size_value, bytes) =>
                                                              Some ({| notification_time := notification_time_value; mpid := mpid_value; product_id := product_id_value; liquidity_type := liquidity_type_value; client_message_id := client_message_id_value; bulk_quote_index := bulk_quote_index_value; event_id := event_id_value; trade_id := trade_id_value; execution_id := execution_id_value; reserved_1 := reserved_1_value; trade_status := trade_status_value; last_price := last_price_value; side := side_value; last_size := last_size_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionExecutionNotification.

  Module StockLegExecutionNotification.

    (** This message format will be used to notify the firm of a stock leg execution from a stock-tied complex eQuote. *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      underlying_symbol : list byte;
      liquidity_type : list byte;
      client_message_id : N;
      event_id : N;
      trade_id : N;
      execution_id : N;
      trade_status : list byte;
      last_price : N;
      side : list byte;
      stock_sell_short_indicator : list byte;
      last_size : N;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (liquidity_type record) = 1 /\
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      (event_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_status record) = 1 /\
      (last_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (stock_sell_short_indicator record) = 1 /\
      (last_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (liquidity_type record) ++
      encode_uint_le 4 (client_message_id record) ++
      encode_uint_le 4 (event_id record) ++
      encode_uint_le 4 (trade_id record) ++
      encode_uint_le 8 (execution_id record) ++
      encode_bytes 1 (trade_status record) ++
      encode_uint_le 4 (last_price record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (stock_sell_short_indicator record) ++
      encode_uint_le 4 (last_size record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (liquidity_type_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_message_id_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (event_id_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (trade_id_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (execution_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_status_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (last_price_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (stock_sell_short_indicator_value, bytes) =>
                                                      match decode_uint_le 4 bytes with
                                                      | None => None
                                                      | Some (last_size_value, bytes) =>
                                                          match decode_bytes 16 bytes with
                                                          | None => None
                                                          | Some (reserved_16_value, bytes) =>
                                                              Some ({| notification_time := notification_time_value; mpid := mpid_value; underlying_symbol := underlying_symbol_value; liquidity_type := liquidity_type_value; client_message_id := client_message_id_value; event_id := event_id_value; trade_id := trade_id_value; execution_id := execution_id_value; trade_status := trade_status_value; last_price := last_price_value; side := side_value; stock_sell_short_indicator := stock_sell_short_indicator_value; last_size := last_size_value; reserved_16 := reserved_16_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockLegExecutionNotification.

  Module SimpleArmSettingsUpdateRequest.

    (** Firms can use this message format to set up their ARM protection settings for each session. Changes to these settings can be made throughout the day. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      action : list byte;
      underlying_symbol : list byte;
      allowable_engagement_percentage : N;
      counting_period : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (action record) = 1 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      (allowable_engagement_percentage record < 256 ^ N.of_nat 4)%N /\
      (counting_period record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (action record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_uint_le 4 (allowable_engagement_percentage record) ++
      encode_uint_le 2 (counting_period record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (action_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (underlying_symbol_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (allowable_engagement_percentage_value, bytes) =>
                          match decode_uint_le 2 bytes with
                          | None => None
                          | Some (counting_period_value, bytes) =>
                              Some ({| client_message_id := client_message_id_value; mpid := mpid_value; action := action_value; underlying_symbol := underlying_symbol_value; allowable_engagement_percentage := allowable_engagement_percentage_value; counting_period := counting_period_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleArmSettingsUpdateRequest.

  Module SimpleArmSettingsUpdateResponse.

    (** MIAX uses this format to respond to the firm with a status of their ARM protection settings request. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      underlying_symbol : list byte;
      arm_settings_update_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (arm_settings_update_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (arm_settings_update_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (arm_settings_update_status_value, bytes) =>
                      Some ({| client_message_id := client_message_id_value; mpid := mpid_value; underlying_symbol := underlying_symbol_value; arm_settings_update_status := arm_settings_update_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleArmSettingsUpdateResponse.

  Module Arm2UnderlyingLevelProtectionSettingsUpdateRequest.

    (** Firms can use this message format to set up their ARM2 Underlying Level protection settings for each session. Changes to these settings can be made throughout the day. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      action : list byte;
      underlying_symbol : list byte;
      arm_threshold_count : N;
      arm_2_counting_period : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (action record) = 1 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      (arm_threshold_count record < 256 ^ N.of_nat 4)%N /\
      (arm_2_counting_period record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (action record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_uint_le 4 (arm_threshold_count record) ++
      encode_uint_le 4 (arm_2_counting_period record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (action_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (underlying_symbol_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (arm_threshold_count_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (arm_2_counting_period_value, bytes) =>
                              Some ({| client_message_id := client_message_id_value; mpid := mpid_value; action := action_value; underlying_symbol := underlying_symbol_value; arm_threshold_count := arm_threshold_count_value; arm_2_counting_period := arm_2_counting_period_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Arm2UnderlyingLevelProtectionSettingsUpdateRequest.

  Module Arm2UnderlyingLevelProtectionSettingsUpdateResponse.

    (** Emerald uses this format to respond to the firm with a status of their ARM2 Underlying level protection Settings Update Request. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      underlying_symbol : list byte;
      arm_settings_update_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (arm_settings_update_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (arm_settings_update_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (arm_settings_update_status_value, bytes) =>
                      Some ({| client_message_id := client_message_id_value; mpid := mpid_value; underlying_symbol := underlying_symbol_value; arm_settings_update_status := arm_settings_update_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Arm2UnderlyingLevelProtectionSettingsUpdateResponse.

  Module SimpleEnhancedQuoteEQuoteMessage.

    (** This is the format for an eQuote message that can be sent either to match with orders and quotes on the Emerald book or when responding to a liquidity seeking event. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      client_send_time : N;
      product_id : N;
      e_quote_action : list byte;
      e_quote_type : list byte;
      event_id : N;
      target_message_id : N;
      price : N;
      size : N;
      side : list byte;
      reserved_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      (client_send_time record < 256 ^ N.of_nat 8)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (e_quote_action record) = 1 /\
      Datatypes.length (e_quote_type record) = 1 /\
      (event_id record < 256 ^ N.of_nat 4)%N /\
      (target_message_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (reserved_4 record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 8 (client_send_time record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 1 (e_quote_action record) ++
      encode_bytes 1 (e_quote_type record) ++
      encode_uint_le 4 (event_id record) ++
      encode_uint_le 4 (target_message_id record) ++
      encode_uint_le 4 (price record) ++
      encode_uint_le 4 (size record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (client_send_time_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (product_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (e_quote_action_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (e_quote_type_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (event_id_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (target_message_id_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (price_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (size_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (reserved_4_value, bytes) =>
                                                      Some ({| client_message_id := client_message_id_value; mpid := mpid_value; client_send_time := client_send_time_value; product_id := product_id_value; e_quote_action := e_quote_action_value; e_quote_type := e_quote_type_value; event_id := event_id_value; target_message_id := target_message_id_value; price := price_value; size := size_value; side := side_value; reserved_4 := reserved_4_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleEnhancedQuoteEQuoteMessage.

  Module ComplexEnhancedQuoteEQuoteMessage.

    (** This is the format for a Complex eQuote message that can be sent either to match with complex book or when responding to a complex auction liquidity seeking event. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      client_send_time : N;
      strategy_id : N;
      e_quote_action : list byte;
      e_quote_type : list byte;
      complex_event_id : N;
      target_message_id : N;
      net_price : N;
      size : N;
      side : list byte;
      stock_sell_short_indicator : list byte;
      reserved_15 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      (client_send_time record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (e_quote_action record) = 1 /\
      Datatypes.length (e_quote_type record) = 1 /\
      (complex_event_id record < 256 ^ N.of_nat 4)%N /\
      (target_message_id record < 256 ^ N.of_nat 4)%N /\
      (net_price record < 256 ^ N.of_nat 8)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (stock_sell_short_indicator record) = 1 /\
      Datatypes.length (reserved_15 record) = 15.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 8 (client_send_time record) ++
      encode_uint_le 4 (strategy_id record) ++
      encode_bytes 1 (e_quote_action record) ++
      encode_bytes 1 (e_quote_type record) ++
      encode_uint_le 4 (complex_event_id record) ++
      encode_uint_le 4 (target_message_id record) ++
      encode_uint_le 8 (net_price record) ++
      encode_uint_le 4 (size record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (stock_sell_short_indicator record) ++
      encode_bytes 15 (reserved_15 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (client_send_time_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (strategy_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (e_quote_action_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (e_quote_type_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (complex_event_id_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (target_message_id_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (net_price_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (size_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (stock_sell_short_indicator_value, bytes) =>
                                                      match decode_bytes 15 bytes with
                                                      | None => None
                                                      | Some (reserved_15_value, bytes) =>
                                                          Some ({| client_message_id := client_message_id_value; mpid := mpid_value; client_send_time := client_send_time_value; strategy_id := strategy_id_value; e_quote_action := e_quote_action_value; e_quote_type := e_quote_type_value; complex_event_id := complex_event_id_value; target_message_id := target_message_id_value; net_price := net_price_value; size := size_value; side := side_value; stock_sell_short_indicator := stock_sell_short_indicator_value; reserved_15 := reserved_15_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexEnhancedQuoteEQuoteMessage.

  Module SimpleMassQuoteCancelRequest.

    (** Firms can use this message format to request the cancelation of all simple quotes and eQuotes for an MPID, or all simple quotes and eQuotes for an MPID for all series for an underlying *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      client_send_time : N;
      underlying_symbol : list byte;
      reserved_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      (client_send_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (reserved_4 record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 8 (client_send_time record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (client_send_time_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (underlying_symbol_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (reserved_4_value, bytes) =>
                          Some ({| client_message_id := client_message_id_value; mpid := mpid_value; client_send_time := client_send_time_value; underlying_symbol := underlying_symbol_value; reserved_4 := reserved_4_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleMassQuoteCancelRequest.

  Module SimpleMassQuoteCancelResponse.

    (** This message format will be used to inform the firm about the status of their previous simple mass quote cancel request. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      simple_mass_quote_cancel_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (simple_mass_quote_cancel_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (simple_mass_quote_cancel_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (simple_mass_quote_cancel_status_value, bytes) =>
                  Some ({| client_message_id := client_message_id_value; mpid := mpid_value; simple_mass_quote_cancel_status := simple_mass_quote_cancel_status_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleMassQuoteCancelResponse.

  Module MassLiquidityCancelRequestSimpleAndComplex.

    (** Firms can use this message format to request the cancellation of all simple quotes and simple/complex eQuotes for an MPID, or all simple quotes and simple/complex eQuotes for an MPID for all series and/or strategies for an underlying *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      client_send_time : N;
      underlying_symbol : list byte;
      simple_mass_cancel : list byte;
      complex_mass_cancel : list byte;
      reserved_8 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      (client_send_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (simple_mass_cancel record) = 1 /\
      Datatypes.length (complex_mass_cancel record) = 1 /\
      Datatypes.length (reserved_8 record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 8 (client_send_time record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (simple_mass_cancel record) ++
      encode_bytes 1 (complex_mass_cancel record) ++
      encode_bytes 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (client_send_time_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (underlying_symbol_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (simple_mass_cancel_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (complex_mass_cancel_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (reserved_8_value, bytes) =>
                                  Some ({| client_message_id := client_message_id_value; mpid := mpid_value; client_send_time := client_send_time_value; underlying_symbol := underlying_symbol_value; simple_mass_cancel := simple_mass_cancel_value; complex_mass_cancel := complex_mass_cancel_value; reserved_8 := reserved_8_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassLiquidityCancelRequestSimpleAndComplex.

  Module MassLiquidityCancelResponse.

    (** This message format will be used to inform the firm about the status of their previous Mass Liquidity Cancel Request. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      simple_mass_liquidity_cancel_status : list byte;
      complex_mass_liquidity_cancel_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (simple_mass_liquidity_cancel_status record) = 1 /\
      Datatypes.length (complex_mass_liquidity_cancel_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (simple_mass_liquidity_cancel_status record) ++
      encode_bytes 1 (complex_mass_liquidity_cancel_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (simple_mass_liquidity_cancel_status_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (complex_mass_liquidity_cancel_status_value, bytes) =>
                      Some ({| client_message_id := client_message_id_value; mpid := mpid_value; simple_mass_liquidity_cancel_status := simple_mass_liquidity_cancel_status_value; complex_mass_liquidity_cancel_status := complex_mass_liquidity_cancel_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassLiquidityCancelResponse.

  Module SimpleQuoteProtectionResetRequest.

    (** Following a quote protection being engaged for a given MPID and underlying, firms must use this message format to reset their Quote Protection in order to start quoting for any option of the specified underlying. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      underlying_symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (underlying_symbol record) = 11.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 11 (underlying_symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  Some ({| client_message_id := client_message_id_value; mpid := mpid_value; underlying_symbol := underlying_symbol_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleQuoteProtectionResetRequest.

  Module SimpleQuoteProtectionResetResponse.

    (** This message format is used to inform the firms of the status of their Simple Quote Protection Reset Request. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      quote_protection_reset_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (quote_protection_reset_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (quote_protection_reset_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (quote_protection_reset_status_value, bytes) =>
                  Some ({| client_message_id := client_message_id_value; mpid := mpid_value; quote_protection_reset_status := quote_protection_reset_status_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleQuoteProtectionResetResponse.

  Module LiquidityProtectionResetRequest.

    (** Following a quote protection being engaged for a given MPID and underlying, firms must use this message format to reset their Complex Liquidity Protection and/or Simple Liquidity Protection in order to start submitting new simple or complex liquidities for any strategy of the specified underlying and/or products of the specified underlying. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      underlying_symbol : list byte;
      simple_liquidity_reset : list byte;
      complex_liquidity_reset : list byte;
      reserved_8 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (simple_liquidity_reset record) = 1 /\
      Datatypes.length (complex_liquidity_reset record) = 1 /\
      Datatypes.length (reserved_8 record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (simple_liquidity_reset record) ++
      encode_bytes 1 (complex_liquidity_reset record) ++
      encode_bytes 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (simple_liquidity_reset_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (complex_liquidity_reset_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (reserved_8_value, bytes) =>
                              Some ({| client_message_id := client_message_id_value; mpid := mpid_value; underlying_symbol := underlying_symbol_value; simple_liquidity_reset := simple_liquidity_reset_value; complex_liquidity_reset := complex_liquidity_reset_value; reserved_8 := reserved_8_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LiquidityProtectionResetRequest.

  Module LiquidityProtectionResetResponse.

    (** Response to the Liquidity Protection Reset Request *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      simple_liquidity_protection_reset_status : list byte;
      complex_liquidity_protection_reset_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (simple_liquidity_protection_reset_status record) = 1 /\
      Datatypes.length (complex_liquidity_protection_reset_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (simple_liquidity_protection_reset_status record) ++
      encode_bytes 1 (complex_liquidity_protection_reset_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (simple_liquidity_protection_reset_status_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (complex_liquidity_protection_reset_status_value, bytes) =>
                      Some ({| client_message_id := client_message_id_value; mpid := mpid_value; simple_liquidity_protection_reset_status := simple_liquidity_protection_reset_status_value; complex_liquidity_protection_reset_status := complex_liquidity_protection_reset_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LiquidityProtectionResetResponse.

  Module SingleSideLiquidityProtectionResetRequest.

    (** Request to reset Single Side Liquidity Protection for the specific Option or Complex Strategy. *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      security_id_scope : list byte;
      security_id : N;
      side : list byte;
      reserved_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (security_id_scope record) = 1 /\
      (security_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (reserved_4 record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (security_id_scope record) ++
      encode_uint_le 4 (security_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_id_scope_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (security_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (reserved_4_value, bytes) =>
                              Some ({| client_message_id := client_message_id_value; mpid := mpid_value; security_id_scope := security_id_scope_value; security_id := security_id_value; side := side_value; reserved_4 := reserved_4_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideLiquidityProtectionResetRequest.

  Module SingleSideLiquidityProtectionResetResponse.

    (** Response to Single Side Liquidity Protection Reset Request *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      reserved_4 : list byte;
      status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (reserved_4 record) = 4 /\
      Datatypes.length (status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 4 (reserved_4 record) ++
      encode_bytes 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (reserved_4_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (status_value, bytes) =>
                      Some ({| client_message_id := client_message_id_value; mpid := mpid_value; reserved_4 := reserved_4_value; status := status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideLiquidityProtectionResetResponse.

  Module SimpleQuoteProtectionTriggerNotification.

    (** This message format will be used to notify firms when an MPID is placed under simple quote protection. Simple Quote protection can be triggered due to any one of the reasons listed in the message below. *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      underlying_symbol : list byte;
      trigger_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (trigger_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (trigger_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trigger_reason_value, bytes) =>
                      Some ({| notification_time := notification_time_value; mpid := mpid_value; underlying_symbol := underlying_symbol_value; trigger_reason := trigger_reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleQuoteProtectionTriggerNotification.

  Module ComplexLiquidityProtectionTriggerNotification.

    (** This message format will be used to notify firms when an MPID is placed under complex liquidity protection. Complex Liquidity protection can be triggered due to any one of the reasons listed in the message below. *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      underlying_symbol : list byte;
      trigger_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (trigger_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (trigger_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trigger_reason_value, bytes) =>
                      Some ({| notification_time := notification_time_value; mpid := mpid_value; underlying_symbol := underlying_symbol_value; trigger_reason := trigger_reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexLiquidityProtectionTriggerNotification.

  Module LoginRequest.

    (** The SesM client uses this packet to allow the server to authenticate the client and to convey to the server the last sequenced packet that the client received *)
    Record t := {
      sesm_version : list byte;
      username : list byte;
      computer_id : list byte;
      application_protocol : list byte;
      requested_session : N;
      requested_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sesm_version record) = 5 /\
      Datatypes.length (username record) = 5 /\
      Datatypes.length (computer_id record) = 8 /\
      Datatypes.length (application_protocol record) = 8 /\
      (requested_session record < 256 ^ N.of_nat 1)%N /\
      (requested_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (sesm_version record) ++
      encode_bytes 5 (username record) ++
      encode_bytes 8 (computer_id record) ++
      encode_bytes 8 (application_protocol record) ++
      encode_uint 1 (requested_session record) ++
      encode_uint_le 8 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (sesm_version_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (username_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (computer_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (application_protocol_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (requested_session_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (requested_sequence_number_value, bytes) =>
                              Some ({| sesm_version := sesm_version_value; username := username_value; computer_id := computer_id_value; application_protocol := application_protocol_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRequest.

  Module LoginResponse.

    (** The SesM server sends a Login response packet in response to a Login request packet from the client *)
    Record t := {
      login_status : list byte;
      session_id : N;
      highest_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (login_status record) = 1 /\
      (session_id record < 256 ^ N.of_nat 1)%N /\
      (highest_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (login_status record) ++
      encode_uint 1 (session_id record) ++
      encode_uint_le 8 (highest_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (login_status_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (session_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (highest_sequence_number_value, bytes) =>
                  Some ({| login_status := login_status_value; session_id := session_id_value; highest_sequence_number := highest_sequence_number_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginResponse.

  Module RetransmissionRequest.

    (** The SesM client uses this packet to request the server to retransmit a range of packets *)
    Record t := {
      start_sequence_number : N;
      end_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (end_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (start_sequence_number record) ++
      encode_uint_le 8 (end_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (start_sequence_number_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (end_sequence_number_value, bytes) =>
              Some ({| start_sequence_number := start_sequence_number_value; end_sequence_number := end_sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RetransmissionRequest.

End EmeraldOptionsExpressInterfaceV23.
