From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings Express Orders

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

Module PearlOptionsExpressOrdersV20C.

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

  Module SeriesUpdate.

    (** This is the message format that will be used to disseminate all Option series traded on Pearl for the current session on the cloud associated for this connection *)
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
      active_on_pearl : list byte;
      pearl_bbo_posting_increment_indicator : list byte;
      order_acceptance_increment_indicator : list byte;
      opening_underlying_market_code : list byte;
      reserved_12 : list byte;
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
      Datatypes.length (active_on_pearl record) = 1 /\
      Datatypes.length (pearl_bbo_posting_increment_indicator record) = 1 /\
      Datatypes.length (order_acceptance_increment_indicator record) = 1 /\
      Datatypes.length (opening_underlying_market_code record) = 1 /\
      Datatypes.length (reserved_12 record) = 12.

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
      encode_bytes 1 (active_on_pearl record) ++
      encode_bytes 1 (pearl_bbo_posting_increment_indicator record) ++
      encode_bytes 1 (order_acceptance_increment_indicator record) ++
      encode_bytes 1 (opening_underlying_market_code record) ++
      encode_bytes 12 (reserved_12 record).

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
                                                  | Some (active_on_pearl_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (pearl_bbo_posting_increment_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (order_acceptance_increment_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (opening_underlying_market_code_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (reserved_12_value, bytes) =>
                                                                      Some ({| product_add_update_time := product_add_update_time_value; product_id := product_id_value; underlying_symbol := underlying_symbol_value; security_symbol := security_symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; call_or_put := call_or_put_value; opening_time := opening_time_value; closing_time := closing_time_value; restricted_option := restricted_option_value; long_term_option := long_term_option_value; active_on_pearl := active_on_pearl_value; pearl_bbo_posting_increment_indicator := pearl_bbo_posting_increment_indicator_value; order_acceptance_increment_indicator := order_acceptance_increment_indicator_value; opening_underlying_market_code := opening_underlying_market_code_value; reserved_12 := reserved_12_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SeriesUpdate.

  Module SystemStateNotification.

    (** This message format is used to notify the firms of the state changes of the system. This is an exchange-wide notification and not a symbol or member-based notification *)
    Record t := {
      notification_time : N;
      meo_version : list byte;
      session_id : N;
      system_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (meo_version record) = 8 /\
      (session_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (system_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 8 (meo_version record) ++
      encode_uint 1 (session_id record) ++
      encode_bytes 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (meo_version_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      Some ({| notification_time := notification_time_value; meo_version := meo_version_value; session_id := session_id_value; system_status := system_status_value |}, bytes)
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

  Module UnderlyingTradingStatusNotification.

    (** This message format will be used to notify the firms of changes to the trading status of all the options of an underlying *)
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

  Module OpeningWidthReliefNotification.

    (** This message format will be used to notify the firms if and when Pearl grants relief from valid opening width parameters for Opening as specified by regulatory circulars of Pearl *)
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

  End OpeningWidthReliefNotification.

  Module ArmProtectionSettingsNotification.

    (** This message format will be used to notify firms of their ARM settings *)
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

  End ArmProtectionSettingsNotification.

  Module Arm2UnderlyingLevelProtectionSettingsNotification.

    (** This message format will be used to notify firms of their ARM2 Underlying Level protection settings *)
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

    (** This message format will be used to notify firms when a Single Side Liquidity Protection is triggered for an Option *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      product_id : N;
      side : list byte;
      triggering_client_message_id : N;
      triggering_bulk_order_index : N;
      reserved_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (triggering_client_message_id record < 256 ^ N.of_nat 4)%N /\
      (triggering_bulk_order_index record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reserved_4 record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint_le 4 (triggering_client_message_id record) ++
      encode_uint 1 (triggering_bulk_order_index record) ++
      encode_bytes 4 (reserved_4 record).

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
                  | Some (side_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (triggering_client_message_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (triggering_bulk_order_index_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (reserved_4_value, bytes) =>
                                  Some ({| notification_time := notification_time_value; mpid := mpid_value; product_id := product_id_value; side := side_value; triggering_client_message_id := triggering_client_message_id_value; triggering_bulk_order_index := triggering_bulk_order_index_value; reserved_4 := reserved_4_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideLiquidityProtectionTriggerNotification.

  Module Arm2UnderlyingLevelProtectionNotification.

    (** This message format will be used to notify firms about ARM2 Underlying Level protection events *)
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

    (** This message format will be used to notify firms about ARM2 Firm Level protection events *)
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

    (** This is the message format that will be used to notify firms about order cancels. By default this is not a sequenced message; firms can request it to be configured as a sequenced message *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      product_id : N;
      liquidity_type : list byte;
      client_message_id : N;
      client_order_id : N;
      bulk_order_index : N;
      side : list byte;
      size : N;
      engine_sequence_number : N;
      cancel_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (liquidity_type record) = 1 /\
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      (client_order_id record < 256 ^ N.of_nat 4)%N /\
      (bulk_order_index record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (side record) = 1 /\
      (size record < 256 ^ N.of_nat 4)%N /\
      (engine_sequence_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cancel_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 1 (liquidity_type record) ++
      encode_uint_le 4 (client_message_id record) ++
      encode_uint_le 4 (client_order_id record) ++
      encode_uint 1 (bulk_order_index record) ++
      encode_bytes 1 (side record) ++
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
              | Some (product_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (liquidity_type_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (client_message_id_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (bulk_order_index_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (size_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (engine_sequence_number_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (cancel_reason_value, bytes) =>
                                                  Some ({| notification_time := notification_time_value; mpid := mpid_value; product_id := product_id_value; liquidity_type := liquidity_type_value; client_message_id := client_message_id_value; client_order_id := client_order_id_value; bulk_order_index := bulk_order_index_value; side := side_value; size := size_value; engine_sequence_number := engine_sequence_number_value; cancel_reason := cancel_reason_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelNotification.

  Module ExecutionNotification.

    (** This message format will be used to notify the firms of executions of their orders *)
    Record t := {
      notification_time : N;
      mpid : list byte;
      product_id : N;
      liquidity_type : list byte;
      client_message_id : N;
      client_order_id : N;
      bulk_order_index : N;
      trade_id : N;
      execution_id : N;
      trade_status : list byte;
      last_price : N;
      side : list byte;
      last_size : N;
      liquidity_indicator : list byte;
      reserved_15 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (liquidity_type record) = 1 /\
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      (client_order_id record < 256 ^ N.of_nat 4)%N /\
      (bulk_order_index record < 256 ^ N.of_nat 1)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_status record) = 1 /\
      (last_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (last_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (liquidity_indicator record) = 1 /\
      Datatypes.length (reserved_15 record) = 15.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 1 (liquidity_type record) ++
      encode_uint_le 4 (client_message_id record) ++
      encode_uint_le 4 (client_order_id record) ++
      encode_uint 1 (bulk_order_index record) ++
      encode_uint_le 4 (trade_id record) ++
      encode_uint_le 8 (execution_id record) ++
      encode_bytes 1 (trade_status record) ++
      encode_uint_le 4 (last_price record) ++
      encode_bytes 1 (side record) ++
      encode_uint_le 4 (last_size record) ++
      encode_bytes 1 (liquidity_indicator record) ++
      encode_bytes 15 (reserved_15 record).

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
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (bulk_order_index_value, bytes) =>
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
                                                      match decode_uint_le 4 bytes with
                                                      | None => None
                                                      | Some (last_size_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (liquidity_indicator_value, bytes) =>
                                                              match decode_bytes 15 bytes with
                                                              | None => None
                                                              | Some (reserved_15_value, bytes) =>
                                                                  Some ({| notification_time := notification_time_value; mpid := mpid_value; product_id := product_id_value; liquidity_type := liquidity_type_value; client_message_id := client_message_id_value; client_order_id := client_order_id_value; bulk_order_index := bulk_order_index_value; trade_id := trade_id_value; execution_id := execution_id_value; trade_status := trade_status_value; last_price := last_price_value; side := side_value; last_size := last_size_value; liquidity_indicator := liquidity_indicator_value; reserved_15 := reserved_15_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionNotification.

  Module ArmSettingsUpdateRequest.

    (** Firms can use this message format to set up their ARM protection settings for each session. Changes to these settings can be made throughout the day *)
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

  End ArmSettingsUpdateRequest.

  Module ArmSettingsUpdateResponse.

    (** Pearl uses this format to respond to the firm with a status of their ARM protection settings request *)
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

  End ArmSettingsUpdateResponse.

  Module Arm2UnderlyingLevelProtectionSettingsUpdateRequest.

    (** Firms can use this message format to set up their ARM2 Underlying Level protection settings for each session. Changes to these settings can be made throughout the day *)
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

    (** Pearl uses this format to respond to the firm with a status of their ARM2 Underlying level protection Settings Update Request *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      underlying_symbol : list byte;
      arm_2_settings_update_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (arm_2_settings_update_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (arm_2_settings_update_status record).

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
                  | Some (arm_2_settings_update_status_value, bytes) =>
                      Some ({| client_message_id := client_message_id_value; mpid := mpid_value; underlying_symbol := underlying_symbol_value; arm_2_settings_update_status := arm_2_settings_update_status_value |}, bytes)
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

  Module SeriesAssignmentRequest.

    (** Market Making firms can use this message format to communicate to Pearl which of their MM MPIDs is assigned or unassigned in a product *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      product_id : N;
      action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 1 (action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (action_value, bytes) =>
                      Some ({| client_message_id := client_message_id_value; mpid := mpid_value; product_id := product_id_value; action := action_value |}, bytes)
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
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SeriesAssignmentRequest.

  Module SeriesAssignmentResponse.

    (** Pearl uses this format to respond to the firm assignment request *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      assignment_settings_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (assignment_settings_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (assignment_settings_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (assignment_settings_status_value, bytes) =>
                  Some ({| client_message_id := client_message_id_value; mpid := mpid_value; assignment_settings_status := assignment_settings_status_value |}, bytes)
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

  End SeriesAssignmentResponse.

  Module SelfTradeProtectionDesignationRequest.

    (** Firms can use this message format to communicate to Pearl which of their EEM MPIDs are designated for self-trade protection *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (action record).

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
                  Some ({| client_message_id := client_message_id_value; mpid := mpid_value; action := action_value |}, bytes)
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

  End SelfTradeProtectionDesignationRequest.

  Module SelfTradeProtectionDesignationResponse.

    (** Pearl uses this format to respond to the firm assignment request *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      self_trade_protection_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (self_trade_protection_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (self_trade_protection_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (self_trade_protection_status_value, bytes) =>
                  Some ({| client_message_id := client_message_id_value; mpid := mpid_value; self_trade_protection_status := self_trade_protection_status_value |}, bytes)
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

  End SelfTradeProtectionDesignationResponse.

  Module LiquidityMassCancelRequest.

    (** Firms can use this message format to request the cancelation of all orders for an MPID for all series for an underlying *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      client_send_time : N;
      underlying_symbol : list byte;
      mass_cancel_scope : list byte;
      reserved_7 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      (client_send_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (mass_cancel_scope record) = 1 /\
      Datatypes.length (reserved_7 record) = 7.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 8 (client_send_time record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (mass_cancel_scope record) ++
      encode_bytes 7 (reserved_7 record).

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
                      | Some (mass_cancel_scope_value, bytes) =>
                          match decode_bytes 7 bytes with
                          | None => None
                          | Some (reserved_7_value, bytes) =>
                              Some ({| client_message_id := client_message_id_value; mpid := mpid_value; client_send_time := client_send_time_value; underlying_symbol := underlying_symbol_value; mass_cancel_scope := mass_cancel_scope_value; reserved_7 := reserved_7_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LiquidityMassCancelRequest.

  Module LiquidityMassCancelResponse.

    (** This message format will be used to inform the firm about the status of their previous Mass Cancel request *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  Some ({| client_message_id := client_message_id_value; mpid := mpid_value; status := status_value |}, bytes)
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

  End LiquidityMassCancelResponse.

  Module LiquidityProtectionResetRequest.

    (** Firms use this message format to reset their Order Protection for an underlying *)
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

  End LiquidityProtectionResetRequest.

  Module LiquidityProtectionResetResponse.

    (** This message format is used to inform the firms of the status of their Order Protection Reset Request *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  Some ({| client_message_id := client_message_id_value; mpid := mpid_value; status := status_value |}, bytes)
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

  End LiquidityProtectionResetResponse.

  Module SingleSideLiquidityProtectionResetRequest.

    (** Request to reset Single Side Liquidity Protection for the specific Option and Side for a given MPID *)
    Record t := {
      client_message_id : N;
      mpid : list byte;
      product_id : N;
      side : list byte;
      reserved_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (reserved_4 record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (client_message_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (client_message_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (reserved_4_value, bytes) =>
                          Some ({| client_message_id := client_message_id_value; mpid := mpid_value; product_id := product_id_value; side := side_value; reserved_4 := reserved_4_value |}, bytes)
                      end
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

  Module LiquidityProtectionTriggerNotification.

    (** This message format will be used to notify firms when order protection is triggered for an MPID *)
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

  End LiquidityProtectionTriggerNotification.

  Module OrderNotification.

    (** This is the message format that will be used to notify firms about orders sent by firms. Note that this is sent for new orders only (including replaces) and it is meant to provide a copy of the order *)
    Record t := {
      notification_time : N;
      client_order_id : N;
      client_message_id : N;
      bulk_order_index : N;
      target_client_order_id : N;
      mpid : list byte;
      product_id : N;
      time_in_force_tif : list byte;
      order_instruction : list byte;
      origin : list byte;
      mvp : N;
      price : N;
      size : N;
      side : list byte;
      open_close : list byte;
      covered_uncovered : list byte;
      clearing_account : list byte;
      cmta : N;
      account : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 4)%N /\
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      (bulk_order_index record < 256 ^ N.of_nat 1)%N /\
      (target_client_order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (time_in_force_tif record) = 1 /\
      Datatypes.length (order_instruction record) = 1 /\
      Datatypes.length (origin record) = 1 /\
      (mvp record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (covered_uncovered record) = 1 /\
      Datatypes.length (clearing_account record) = 5 /\
      (cmta record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_uint_le 4 (client_order_id record) ++
      encode_uint_le 4 (client_message_id record) ++
      encode_uint 1 (bulk_order_index record) ++
      encode_uint_le 4 (target_client_order_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 1 (time_in_force_tif record) ++
      encode_bytes 1 (order_instruction record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 1 (mvp record) ++
      encode_uint_le 4 (price record) ++
      encode_uint_le 4 (size record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (covered_uncovered record) ++
      encode_bytes 5 (clearing_account record) ++
      encode_uint_le 4 (cmta record) ++
      encode_bytes 10 (account record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (client_order_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (client_message_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (bulk_order_index_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (target_client_order_id_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (mpid_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (product_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (time_in_force_tif_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (order_instruction_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (origin_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (mvp_value, bytes) =>
                                                  match decode_uint_le 4 bytes with
                                                  | None => None
                                                  | Some (price_value, bytes) =>
                                                      match decode_uint_le 4 bytes with
                                                      | None => None
                                                      | Some (size_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (side_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (open_close_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (covered_uncovered_value, bytes) =>
                                                                      match decode_bytes 5 bytes with
                                                                      | None => None
                                                                      | Some (clearing_account_value, bytes) =>
                                                                          match decode_uint_le 4 bytes with
                                                                          | None => None
                                                                          | Some (cmta_value, bytes) =>
                                                                              match decode_bytes 10 bytes with
                                                                              | None => None
                                                                              | Some (account_value, bytes) =>
                                                                                  Some ({| notification_time := notification_time_value; client_order_id := client_order_id_value; client_message_id := client_message_id_value; bulk_order_index := bulk_order_index_value; target_client_order_id := target_client_order_id_value; mpid := mpid_value; product_id := product_id_value; time_in_force_tif := time_in_force_tif_value; order_instruction := order_instruction_value; origin := origin_value; mvp := mvp_value; price := price_value; size := size_value; side := side_value; open_close := open_close_value; covered_uncovered := covered_uncovered_value; clearing_account := clearing_account_value; cmta := cmta_value; account := account_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint_le by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderNotification.

  Module DoneForTheDayNotification.

    (** This is the message format that will be used to notify firms about the final status of the binary orders at the end of day after end of LOW *)
    Record t := {
      notification_time : N;
      client_order_id : N;
      client_message_id : N;
      bulk_order_index : N;
      target_client_order_id : N;
      mpid : list byte;
      product_id : N;
      time_in_force_tif : list byte;
      order_instruction : list byte;
      origin : list byte;
      mvp : N;
      price : N;
      size : N;
      side : list byte;
      open_close : list byte;
      covered_uncovered : list byte;
      clearing_account : list byte;
      cmta : N;
      account : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 4)%N /\
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      (bulk_order_index record < 256 ^ N.of_nat 1)%N /\
      (target_client_order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (time_in_force_tif record) = 1 /\
      Datatypes.length (order_instruction record) = 1 /\
      Datatypes.length (origin record) = 1 /\
      (mvp record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (covered_uncovered record) = 1 /\
      Datatypes.length (clearing_account record) = 5 /\
      (cmta record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_uint_le 4 (client_order_id record) ++
      encode_uint_le 4 (client_message_id record) ++
      encode_uint 1 (bulk_order_index record) ++
      encode_uint_le 4 (target_client_order_id record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 1 (time_in_force_tif record) ++
      encode_bytes 1 (order_instruction record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 1 (mvp record) ++
      encode_uint_le 4 (price record) ++
      encode_uint_le 4 (size record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (covered_uncovered record) ++
      encode_bytes 5 (clearing_account record) ++
      encode_uint_le 4 (cmta record) ++
      encode_bytes 10 (account record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (client_order_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (client_message_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (bulk_order_index_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (target_client_order_id_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (mpid_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (product_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (time_in_force_tif_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (order_instruction_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (origin_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (mvp_value, bytes) =>
                                                  match decode_uint_le 4 bytes with
                                                  | None => None
                                                  | Some (price_value, bytes) =>
                                                      match decode_uint_le 4 bytes with
                                                      | None => None
                                                      | Some (size_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (side_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (open_close_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (covered_uncovered_value, bytes) =>
                                                                      match decode_bytes 5 bytes with
                                                                      | None => None
                                                                      | Some (clearing_account_value, bytes) =>
                                                                          match decode_uint_le 4 bytes with
                                                                          | None => None
                                                                          | Some (cmta_value, bytes) =>
                                                                              match decode_bytes 10 bytes with
                                                                              | None => None
                                                                              | Some (account_value, bytes) =>
                                                                                  Some ({| notification_time := notification_time_value; client_order_id := client_order_id_value; client_message_id := client_message_id_value; bulk_order_index := bulk_order_index_value; target_client_order_id := target_client_order_id_value; mpid := mpid_value; product_id := product_id_value; time_in_force_tif := time_in_force_tif_value; order_instruction := order_instruction_value; origin := origin_value; mvp := mvp_value; price := price_value; size := size_value; side := side_value; open_close := open_close_value; covered_uncovered := covered_uncovered_value; clearing_account := clearing_account_value; cmta := cmta_value; account := account_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint_le by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DoneForTheDayNotification.

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

End PearlOptionsExpressOrdersV20C.
