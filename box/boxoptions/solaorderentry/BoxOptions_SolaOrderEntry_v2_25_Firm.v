From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Box Options Market Sola Order Entry

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
      - a run counted by a field
  *)

Module BoxOptionsSolaOrderEntryV225Firm.

  Module IncomingHeader.

    (** The header on all incoming participant business messages *)
    Record t := {
      message_type : list byte;
      user_time : list byte;
      trader_id : list byte;
      user_sequence_i_d : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_type record) = 2 /\
      Datatypes.length (user_time record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_i_d record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (message_type record) ++
      encode_bytes 6 (user_time record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_i_d record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (message_type_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (user_time_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (user_sequence_i_d_value, bytes) =>
                      Some ({| message_type := message_type_value; user_time := user_time_value; trader_id := trader_id_value; user_sequence_i_d := user_sequence_i_d_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IncomingHeader.

  Module UserDisconnection.

    Record t := {
      user_id : list byte;
      session_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 8 /\
      Datatypes.length (session_id record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (user_id record) ++
      encode_bytes 4 (session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (session_id_value, bytes) =>
              Some ({| user_id := user_id_value; session_id := session_id_value |}, bytes)
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

  End UserDisconnection.

  Module HeartbeatResponse.

    (** Stated by the guide as having the same number of bytes and format as TH, whose fields are written out here. *)
    Record t := {
      first_user_sequence_i_d : list byte;
      last_exchange_message_id_sent_to_participant : list byte;
      time_local : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (first_user_sequence_i_d record) = 8 /\
      Datatypes.length (last_exchange_message_id_sent_to_participant record) = 6 /\
      Datatypes.length (time_local record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (first_user_sequence_i_d record) ++
      encode_bytes 6 (last_exchange_message_id_sent_to_participant record) ++
      encode_bytes 6 (time_local record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (first_user_sequence_i_d_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (last_exchange_message_id_sent_to_participant_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (time_local_value, bytes) =>
                  Some ({| first_user_sequence_i_d := first_user_sequence_i_d_value; last_exchange_message_id_sent_to_participant := last_exchange_message_id_sent_to_participant_value; time_local := time_local_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End HeartbeatResponse.

  Module ClearingData.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData.

  Module OwnerData.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OwnerData.

  Module BulkQuoteData.

    Record t := {
      group : list byte;
      clearing_data : ClearingData.t;
      owner_data : OwnerData.t;
      reserved_2 : N;
      reserved_8 : N;
      second_reserved_2 : N;
      calculation_time_interval : list byte;
      maximum_total_volume : list byte;
      maximum_total_value : list byte;
      maximum_delta_volume : list byte;
      maximum_delta_value : list byte;
      percent_of_quote : list byte;
      post_trading_instructions : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      ClearingData.bounded (clearing_data record) /\
      OwnerData.bounded (owner_data record) /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      (second_reserved_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (calculation_time_interval record) = 8 /\
      Datatypes.length (maximum_total_volume record) = 8 /\
      Datatypes.length (maximum_total_value record) = 8 /\
      Datatypes.length (maximum_delta_volume record) = 8 /\
      Datatypes.length (maximum_delta_value record) = 8 /\
      Datatypes.length (percent_of_quote record) = 8 /\
      Datatypes.length (post_trading_instructions record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      ClearingData.encode (clearing_data record) ++
      OwnerData.encode (owner_data record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_uint 8 (reserved_8 record) ++
      encode_uint 2 (second_reserved_2 record) ++
      encode_bytes 8 (calculation_time_interval record) ++
      encode_bytes 8 (maximum_total_volume record) ++
      encode_bytes 8 (maximum_total_value record) ++
      encode_bytes 8 (maximum_delta_volume record) ++
      encode_bytes 8 (maximum_delta_value record) ++
      encode_bytes 8 (percent_of_quote record) ++
      encode_bytes 50 (post_trading_instructions record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match ClearingData.decode bytes with
          | None => None
          | Some (clearing_data_value, bytes) =>
              match OwnerData.decode bytes with
              | None => None
              | Some (owner_data_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (reserved_2_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (reserved_8_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (second_reserved_2_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (calculation_time_interval_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (maximum_total_volume_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (maximum_total_value_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (maximum_delta_volume_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (maximum_delta_value_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (percent_of_quote_value, bytes) =>
                                                      match decode_bytes 50 bytes with
                                                      | None => None
                                                      | Some (post_trading_instructions_value, bytes) =>
                                                          Some ({| group := group_value; clearing_data := clearing_data_value; owner_data := owner_data_value; reserved_2 := reserved_2_value; reserved_8 := reserved_8_value; second_reserved_2 := second_reserved_2_value; calculation_time_interval := calculation_time_interval_value; maximum_total_volume := maximum_total_volume_value; maximum_total_value := maximum_total_value_value; maximum_delta_volume := maximum_delta_volume_value; maximum_delta_value := maximum_delta_value_value; percent_of_quote := percent_of_quote_value; post_trading_instructions := post_trading_instructions_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !ClearingData.encode_length, !OwnerData.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ClearingData.decode_encode by exact bound_1.
      rewrite OwnerData.decode_encode by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData.eq_dec | apply OwnerData.eq_dec]. Defined.

  End BulkQuoteData.

  Module GlobalCancellation.

    Record t := {
      group : list byte;
      type_of_cancellation : list byte;
      mm_cat_user_time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (type_of_cancellation record) = 1 /\
      Datatypes.length (mm_cat_user_time record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 1 (type_of_cancellation record) ++
      encode_bytes 8 (mm_cat_user_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (type_of_cancellation_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (mm_cat_user_time_value, bytes) =>
                  Some ({| group := group_value; type_of_cancellation := type_of_cancellation_value; mm_cat_user_time := mm_cat_user_time_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GlobalCancellation.

  Module UserGlobalCancellation.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      type_of_cancellation : list byte;
      account_type_filter : list byte;
      mm_cat_user_time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (type_of_cancellation record) = 1 /\
      Datatypes.length (account_type_filter record) = 8 /\
      Datatypes.length (mm_cat_user_time record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 1 (type_of_cancellation record) ++
      encode_bytes 8 (account_type_filter record) ++
      encode_bytes 8 (mm_cat_user_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (type_of_cancellation_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (account_type_filter_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (mm_cat_user_time_value, bytes) =>
                          Some ({| group := group_value; instrument_optional := instrument_optional_value; type_of_cancellation := type_of_cancellation_value; account_type_filter := account_type_filter_value; mm_cat_user_time := mm_cat_user_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UserGlobalCancellation.

  Module DirectedRoutedOrderRejectionAndQuote.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      order_id : list byte;
      rejection_code : list byte;
      quote_quantity : list byte;
      quote_price : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (rejection_code record) = 4 /\
      Datatypes.length (quote_quantity record) = 8 /\
      Datatypes.length (quote_price record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 4 (rejection_code record) ++
      encode_bytes 8 (quote_quantity record) ++
      encode_bytes 10 (quote_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (rejection_code_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (quote_quantity_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (quote_price_value, bytes) =>
                                  Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; order_id := order_id_value; rejection_code := rejection_code_value; quote_quantity := quote_quantity_value; quote_price := quote_price_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DirectedRoutedOrderRejectionAndQuote.

  Module BuyingClearingData.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BuyingClearingData.

  Module SellingClearingData.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SellingClearingData.

  Module BuyingOwnerData.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BuyingOwnerData.

  Module SellingOwnerData.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SellingOwnerData.

  Module AuctionEntry.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      verb_side : list byte;
      quantity : list byte;
      price : list byte;
      buying_clearing_data : BuyingClearingData.t;
      selling_clearing_data : SellingClearingData.t;
      buying_owner_data : BuyingOwnerData.t;
      selling_owner_data : SellingOwnerData.t;
      iml_handling : list byte;
      special_price_term : list byte;
      additional_price : list byte;
      quantity_term : list byte;
      additional_quantity : list byte;
      buying_post_trading_instruction : list byte;
      selling_post_trading_instruction : list byte;
      buying_additional_client_memo : list byte;
      selling_additional_client_memo : list byte;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (price record) = 10 /\
      BuyingClearingData.bounded (buying_clearing_data record) /\
      SellingClearingData.bounded (selling_clearing_data record) /\
      BuyingOwnerData.bounded (buying_owner_data record) /\
      SellingOwnerData.bounded (selling_owner_data record) /\
      Datatypes.length (iml_handling record) = 1 /\
      Datatypes.length (special_price_term record) = 1 /\
      Datatypes.length (additional_price record) = 10 /\
      Datatypes.length (quantity_term record) = 1 /\
      Datatypes.length (additional_quantity record) = 8 /\
      Datatypes.length (buying_post_trading_instruction record) = 50 /\
      Datatypes.length (selling_post_trading_instruction record) = 50 /\
      Datatypes.length (buying_additional_client_memo record) = 16 /\
      Datatypes.length (selling_additional_client_memo record) = 16 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (price record) ++
      BuyingClearingData.encode (buying_clearing_data record) ++
      SellingClearingData.encode (selling_clearing_data record) ++
      BuyingOwnerData.encode (buying_owner_data record) ++
      SellingOwnerData.encode (selling_owner_data record) ++
      encode_bytes 1 (iml_handling record) ++
      encode_bytes 1 (special_price_term record) ++
      encode_bytes 10 (additional_price record) ++
      encode_bytes 1 (quantity_term record) ++
      encode_bytes 8 (additional_quantity record) ++
      encode_bytes 50 (buying_post_trading_instruction record) ++
      encode_bytes 50 (selling_post_trading_instruction record) ++
      encode_bytes 16 (buying_additional_client_memo record) ++
      encode_bytes 16 (selling_additional_client_memo record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (verb_side_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match BuyingClearingData.decode bytes with
                          | None => None
                          | Some (buying_clearing_data_value, bytes) =>
                              match SellingClearingData.decode bytes with
                              | None => None
                              | Some (selling_clearing_data_value, bytes) =>
                                  match BuyingOwnerData.decode bytes with
                                  | None => None
                                  | Some (buying_owner_data_value, bytes) =>
                                      match SellingOwnerData.decode bytes with
                                      | None => None
                                      | Some (selling_owner_data_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (iml_handling_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (special_price_term_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (additional_price_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (quantity_term_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (additional_quantity_value, bytes) =>
                                                              match decode_bytes 50 bytes with
                                                              | None => None
                                                              | Some (buying_post_trading_instruction_value, bytes) =>
                                                                  match decode_bytes 50 bytes with
                                                                  | None => None
                                                                  | Some (selling_post_trading_instruction_value, bytes) =>
                                                                      match decode_bytes 16 bytes with
                                                                      | None => None
                                                                      | Some (buying_additional_client_memo_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (selling_additional_client_memo_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (reserved_4_value, bytes) =>
                                                                                  Some ({| group := group_value; instrument_optional := instrument_optional_value; verb_side := verb_side_value; quantity := quantity_value; price := price_value; buying_clearing_data := buying_clearing_data_value; selling_clearing_data := selling_clearing_data_value; buying_owner_data := buying_owner_data_value; selling_owner_data := selling_owner_data_value; iml_handling := iml_handling_value; special_price_term := special_price_term_value; additional_price := additional_price_value; quantity_term := quantity_term_value; additional_quantity := additional_quantity_value; buying_post_trading_instruction := buying_post_trading_instruction_value; selling_post_trading_instruction := selling_post_trading_instruction_value; buying_additional_client_memo := buying_additional_client_memo_value; selling_additional_client_memo := selling_additional_client_memo_value; reserved_4 := reserved_4_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 364.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !BuyingClearingData.encode_length, !SellingClearingData.encode_length, !BuyingOwnerData.encode_length, !SellingOwnerData.encode_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite BuyingClearingData.decode_encode by exact bound_5.
      rewrite SellingClearingData.decode_encode by exact bound_6.
      rewrite BuyingOwnerData.decode_encode by exact bound_7.
      rewrite SellingOwnerData.decode_encode by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply BuyingClearingData.eq_dec | apply SellingClearingData.eq_dec | apply BuyingOwnerData.eq_dec | apply SellingOwnerData.eq_dec]. Defined.

  End AuctionEntry.

  Module ClearingDataDealer.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingDataDealer.

  Module OwnerDataDealer.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OwnerDataDealer.

  Module DirectedOrderAcceptation.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      referenced_order_id : list byte;
      auction_starting_price : list byte;
      clearing_data_dealer : ClearingDataDealer.t;
      owner_data_dealer : OwnerDataDealer.t;
      additional_price : list byte;
      quantity_term : list byte;
      post_trading_instruction : list byte;
      additional_quantity : list byte;
      additional_client_memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (referenced_order_id record) = 8 /\
      Datatypes.length (auction_starting_price record) = 10 /\
      ClearingDataDealer.bounded (clearing_data_dealer record) /\
      OwnerDataDealer.bounded (owner_data_dealer record) /\
      Datatypes.length (additional_price record) = 10 /\
      Datatypes.length (quantity_term record) = 1 /\
      Datatypes.length (post_trading_instruction record) = 50 /\
      Datatypes.length (additional_quantity record) = 8 /\
      Datatypes.length (additional_client_memo record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (referenced_order_id record) ++
      encode_bytes 10 (auction_starting_price record) ++
      ClearingDataDealer.encode (clearing_data_dealer record) ++
      OwnerDataDealer.encode (owner_data_dealer record) ++
      encode_bytes 10 (additional_price record) ++
      encode_bytes 1 (quantity_term record) ++
      encode_bytes 50 (post_trading_instruction record) ++
      encode_bytes 8 (additional_quantity record) ++
      encode_bytes 16 (additional_client_memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (referenced_order_id_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (auction_starting_price_value, bytes) =>
                      match ClearingDataDealer.decode bytes with
                      | None => None
                      | Some (clearing_data_dealer_value, bytes) =>
                          match OwnerDataDealer.decode bytes with
                          | None => None
                          | Some (owner_data_dealer_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (additional_price_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (quantity_term_value, bytes) =>
                                      match decode_bytes 50 bytes with
                                      | None => None
                                      | Some (post_trading_instruction_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (additional_quantity_value, bytes) =>
                                              match decode_bytes 16 bytes with
                                              | None => None
                                              | Some (additional_client_memo_value, bytes) =>
                                                  Some ({| group := group_value; instrument_optional := instrument_optional_value; referenced_order_id := referenced_order_id_value; auction_starting_price := auction_starting_price_value; clearing_data_dealer := clearing_data_dealer_value; owner_data_dealer := owner_data_dealer_value; additional_price := additional_price_value; quantity_term := quantity_term_value; post_trading_instruction := post_trading_instruction_value; additional_quantity := additional_quantity_value; additional_client_memo := additional_client_memo_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 200.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingDataDealer.encode_length, !OwnerDataDealer.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite ClearingDataDealer.decode_encode by exact bound_4.
      rewrite OwnerDataDealer.decode_encode by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingDataDealer.eq_dec | apply OwnerDataDealer.eq_dec]. Defined.

  End DirectedOrderAcceptation.

  Module ClearingData2.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData2.

  Module OwnerData2.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OwnerData2.

  Module OrderEntry.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      price_type : list byte;
      verb_side : list byte;
      quantity : list byte;
      price : list byte;
      special_price_term : list byte;
      reserved_10 : list byte;
      quantity_term : list byte;
      additional_quantity : list byte;
      duration_type : list byte;
      gtd_date : list byte;
      executing_participant : list byte;
      iml_handling : list byte;
      clearing_data : ClearingData2.t;
      owner_data : OwnerData2.t;
      post_trading_instructions : list byte;
      additional_client_memo : list byte;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (special_price_term record) = 1 /\
      Datatypes.length (reserved_10 record) = 10 /\
      Datatypes.length (quantity_term record) = 1 /\
      Datatypes.length (additional_quantity record) = 8 /\
      Datatypes.length (duration_type record) = 1 /\
      Datatypes.length (gtd_date record) = 8 /\
      Datatypes.length (executing_participant record) = 4 /\
      Datatypes.length (iml_handling record) = 1 /\
      ClearingData2.bounded (clearing_data record) /\
      OwnerData2.bounded (owner_data record) /\
      Datatypes.length (post_trading_instructions record) = 50 /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 1 (special_price_term record) ++
      encode_bytes 10 (reserved_10 record) ++
      encode_bytes 1 (quantity_term record) ++
      encode_bytes 8 (additional_quantity record) ++
      encode_bytes 1 (duration_type record) ++
      encode_bytes 8 (gtd_date record) ++
      encode_bytes 4 (executing_participant record) ++
      encode_bytes 1 (iml_handling record) ++
      ClearingData2.encode (clearing_data record) ++
      OwnerData2.encode (owner_data record) ++
      encode_bytes 50 (post_trading_instructions record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (price_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (verb_side_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (special_price_term_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (reserved_10_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (quantity_term_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (additional_quantity_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (duration_type_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (gtd_date_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (executing_participant_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (iml_handling_value, bytes) =>
                                                              match ClearingData2.decode bytes with
                                                              | None => None
                                                              | Some (clearing_data_value, bytes) =>
                                                                  match OwnerData2.decode bytes with
                                                                  | None => None
                                                                  | Some (owner_data_value, bytes) =>
                                                                      match decode_bytes 50 bytes with
                                                                      | None => None
                                                                      | Some (post_trading_instructions_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (additional_client_memo_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (reserved_4_value, bytes) =>
                                                                                  Some ({| group := group_value; instrument_optional := instrument_optional_value; price_type := price_type_value; verb_side := verb_side_value; quantity := quantity_value; price := price_value; special_price_term := special_price_term_value; reserved_10 := reserved_10_value; quantity_term := quantity_term_value; additional_quantity := additional_quantity_value; duration_type := duration_type_value; gtd_date := gtd_date_value; executing_participant := executing_participant_value; iml_handling := iml_handling_value; clearing_data := clearing_data_value; owner_data := owner_data_value; post_trading_instructions := post_trading_instructions_value; additional_client_memo := additional_client_memo_value; reserved_4 := reserved_4_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 221.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData2.encode_length, !OwnerData2.encode_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite ClearingData2.decode_encode by exact bound_14.
      rewrite OwnerData2.decode_encode by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData2.eq_dec | apply OwnerData2.eq_dec]. Defined.

  End OrderEntry.

  Module ClearingData3.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData3.

  Module OwnerData3.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OwnerData3.

  Module ImprovementOrderEntry.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      verb_side : list byte;
      quantity_sign : list byte;
      quantity : list byte;
      price : list byte;
      auction_i_d_optional : list byte;
      reserved_17 : list byte;
      clearing_data : ClearingData3.t;
      owner_data : OwnerData3.t;
      post_trading_instructions : list byte;
      additional_client_memo : list byte;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_sign record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (auction_i_d_optional record) = 6 /\
      Datatypes.length (reserved_17 record) = 17 /\
      ClearingData3.bounded (clearing_data record) /\
      OwnerData3.bounded (owner_data record) /\
      Datatypes.length (post_trading_instructions record) = 50 /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 1 (quantity_sign record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 6 (auction_i_d_optional record) ++
      encode_bytes 17 (reserved_17 record) ++
      ClearingData3.encode (clearing_data record) ++
      OwnerData3.encode (owner_data record) ++
      encode_bytes 50 (post_trading_instructions record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (verb_side_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (quantity_sign_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (auction_i_d_optional_value, bytes) =>
                                  match decode_bytes 17 bytes with
                                  | None => None
                                  | Some (reserved_17_value, bytes) =>
                                      match ClearingData3.decode bytes with
                                      | None => None
                                      | Some (clearing_data_value, bytes) =>
                                          match OwnerData3.decode bytes with
                                          | None => None
                                          | Some (owner_data_value, bytes) =>
                                              match decode_bytes 50 bytes with
                                              | None => None
                                              | Some (post_trading_instructions_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (additional_client_memo_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (reserved_4_value, bytes) =>
                                                          Some ({| group := group_value; instrument_optional := instrument_optional_value; verb_side := verb_side_value; quantity_sign := quantity_sign_value; quantity := quantity_value; price := price_value; auction_i_d_optional := auction_i_d_optional_value; reserved_17 := reserved_17_value; clearing_data := clearing_data_value; owner_data := owner_data_value; post_trading_instructions := post_trading_instructions_value; additional_client_memo := additional_client_memo_value; reserved_4 := reserved_4_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 210.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData3.encode_length, !OwnerData3.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData3.decode_encode by exact bound_8.
      rewrite OwnerData3.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData3.eq_dec | apply OwnerData3.eq_dec]. Defined.

  End ImprovementOrderEntry.

  Module ClearingData4.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData4.

  Module OwnerData4.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OwnerData4.

  Module OrderModification.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      price_type : list byte;
      verb_side : list byte;
      quantity_sign : list byte;
      quantity : list byte;
      price : list byte;
      special_price_term : list byte;
      reserved_10 : list byte;
      reserved_1 : N;
      reserved_8 : N;
      duration_type : list byte;
      gtd_date : list byte;
      firm_id : list byte;
      iml_handling : list byte;
      modified_order_id : list byte;
      clearing_data : ClearingData4.t;
      owner_data : OwnerData4.t;
      post_trading_instruction : list byte;
      additional_client_memo : list byte;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_sign record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (special_price_term record) = 1 /\
      Datatypes.length (reserved_10 record) = 10 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (duration_type record) = 1 /\
      Datatypes.length (gtd_date record) = 8 /\
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (iml_handling record) = 1 /\
      Datatypes.length (modified_order_id record) = 8 /\
      ClearingData4.bounded (clearing_data record) /\
      OwnerData4.bounded (owner_data record) /\
      Datatypes.length (post_trading_instruction record) = 50 /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 1 (quantity_sign record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 1 (special_price_term record) ++
      encode_bytes 10 (reserved_10 record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 8 (reserved_8 record) ++
      encode_bytes 1 (duration_type record) ++
      encode_bytes 8 (gtd_date record) ++
      encode_bytes 4 (firm_id record) ++
      encode_bytes 1 (iml_handling record) ++
      encode_bytes 8 (modified_order_id record) ++
      ClearingData4.encode (clearing_data record) ++
      OwnerData4.encode (owner_data record) ++
      encode_bytes 50 (post_trading_instruction record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (price_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (verb_side_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (quantity_sign_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (special_price_term_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (reserved_10_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (reserved_1_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (reserved_8_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (duration_type_value, bytes) =>
                                                      match decode_bytes 8 bytes with
                                                      | None => None
                                                      | Some (gtd_date_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (firm_id_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (iml_handling_value, bytes) =>
                                                                  match decode_bytes 8 bytes with
                                                                  | None => None
                                                                  | Some (modified_order_id_value, bytes) =>
                                                                      match ClearingData4.decode bytes with
                                                                      | None => None
                                                                      | Some (clearing_data_value, bytes) =>
                                                                          match OwnerData4.decode bytes with
                                                                          | None => None
                                                                          | Some (owner_data_value, bytes) =>
                                                                              match decode_bytes 50 bytes with
                                                                              | None => None
                                                                              | Some (post_trading_instruction_value, bytes) =>
                                                                                  match decode_bytes 16 bytes with
                                                                                  | None => None
                                                                                  | Some (additional_client_memo_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (reserved_4_value, bytes) =>
                                                                                          Some ({| group := group_value; instrument_optional := instrument_optional_value; price_type := price_type_value; verb_side := verb_side_value; quantity_sign := quantity_sign_value; quantity := quantity_value; price := price_value; special_price_term := special_price_term_value; reserved_10 := reserved_10_value; reserved_1 := reserved_1_value; reserved_8 := reserved_8_value; duration_type := duration_type_value; gtd_date := gtd_date_value; firm_id := firm_id_value; iml_handling := iml_handling_value; modified_order_id := modified_order_id_value; clearing_data := clearing_data_value; owner_data := owner_data_value; post_trading_instruction := post_trading_instruction_value; additional_client_memo := additional_client_memo_value; reserved_4 := reserved_4_value |}, bytes)
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 230.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !ClearingData4.encode_length, !OwnerData4.encode_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
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
      rewrite ClearingData4.decode_encode by exact bound_16.
      rewrite OwnerData4.decode_encode by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData4.eq_dec | apply OwnerData4.eq_dec]. Defined.

  End OrderModification.

  Module BuyingClearingData2.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BuyingClearingData2.

  Module SellingClearingData2.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SellingClearingData2.

  Module BuyingOwnerData2.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BuyingOwnerData2.

  Module SellingOwnerData2.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SellingOwnerData2.

  Module MarketMakerProtectionSubscription.

    Record t := {
      group : list byte;
      protection_type_advanced_normal : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (protection_type_advanced_normal record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 1 (protection_type_advanced_normal record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (protection_type_advanced_normal_value, bytes) =>
              Some ({| group := group_value; protection_type_advanced_normal := protection_type_advanced_normal_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End MarketMakerProtectionSubscription.

  Module RequestForQuote.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      quantity_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (quantity_1 record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (quantity_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (quantity_1_value, bytes) =>
                  Some ({| group := group_value; instrument_optional := instrument_optional_value; quantity_1 := quantity_1_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RequestForQuote.

  Module OrderCancellation.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      cancelled_order_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (cancelled_order_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (cancelled_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (cancelled_order_id_value, bytes) =>
                  Some ({| group := group_value; instrument_optional := instrument_optional_value; cancelled_order_id := cancelled_order_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancellation.

  Module ImprovementOrderCancellation.

    (** Stated by the guide as having the same number of bytes and format as XE, whose fields are written out here. *)
    Record t := {
      group : list byte;
      instrument_optional : list byte;
      cancelled_order_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (cancelled_order_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (cancelled_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (cancelled_order_id_value, bytes) =>
                  Some ({| group := group_value; instrument_optional := instrument_optional_value; cancelled_order_id := cancelled_order_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ImprovementOrderCancellation.

End BoxOptionsSolaOrderEntryV225Firm.
