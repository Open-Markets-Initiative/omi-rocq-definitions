From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Stock Exchange of India Ltd 

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
      - a run counted by a field
      - a Conversion rule
      - a field read in bits
      - a Composite rule
      - the dispatch that chooses a message by its type
  *)

Module NseFoBroadcastV950.

  Module BcastHeader.

    (** BCAST_HEADER *)
    Record t := {
      reserved_0 : N;
      reserved_2 : N;
      log_time : N;
      alpha_char : list byte;
      transaction_code : N;
      error_code : N;
      bc_seq_no : N;
      reserved_18 : N;
      reserved_19 : N;
      time_stamp_2 : list byte;
      filler_2 : N;
      message_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_0 record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      (log_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (alpha_char record) = 2 /\
      (transaction_code record < 256 ^ N.of_nat 2)%N /\
      (error_code record < 256 ^ N.of_nat 2)%N /\
      (bc_seq_no record < 256 ^ N.of_nat 4)%N /\
      (reserved_18 record < 256 ^ N.of_nat 1)%N /\
      (reserved_19 record < 256 ^ N.of_nat 3)%N /\
      Datatypes.length (time_stamp_2 record) = 8 /\
      (filler_2 record < 256 ^ N.of_nat 8)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (reserved_0 record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_uint 4 (log_time record) ++
      encode_bytes 2 (alpha_char record) ++
      encode_uint 2 (transaction_code record) ++
      encode_uint 2 (error_code record) ++
      encode_uint 4 (bc_seq_no record) ++
      encode_uint 1 (reserved_18 record) ++
      encode_uint 3 (reserved_19 record) ++
      encode_bytes 8 (time_stamp_2 record) ++
      encode_uint 8 (filler_2 record) ++
      encode_uint 2 (message_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (reserved_0_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (reserved_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (log_time_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (alpha_char_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (transaction_code_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (error_code_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (bc_seq_no_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (reserved_18_value, bytes) =>
                                      match decode_uint 3 bytes with
                                      | None => None
                                      | Some (reserved_19_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (time_stamp_2_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (filler_2_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (message_length_value, bytes) =>
                                                      Some ({| reserved_0 := reserved_0_value; reserved_2 := reserved_2_value; log_time := log_time_value; alpha_char := alpha_char_value; transaction_code := transaction_code_value; error_code := error_code_value; bc_seq_no := bc_seq_no_value; reserved_18 := reserved_18_value; reserved_19 := reserved_19_value; time_stamp_2 := time_stamp_2_value; filler_2 := filler_2_value; message_length := message_length_value |}, bytes)
                                                  end
                                              end
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
      rewrite decode_encode_bytes by exact bound_3.
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

  End BcastHeader.

  Module SecurityOpenPriceMessage.

    (** Carries the open price of a security once it opens *)
    Record t := {
      symbol : list byte;
      series : list byte;
      token : N;
      opening_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2 /\
      (token record < 256 ^ N.of_nat 4)%N /\
      (opening_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record) ++
      encode_uint 4 (token record) ++
      encode_uint 4 (opening_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (token_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (opening_price_value, bytes) =>
                      Some ({| symbol := symbol_value; series := series_value; token := token_value; opening_price := opening_price_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityOpenPriceMessage.

  Module SecInfo.

    (** SEC_INFO *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      series : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (series_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (expiry_date_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (strike_price_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (option_type_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ca_level_value, bytes) =>
                                  Some ({| instrument_name := instrument_name_value; symbol := symbol_value; series := series_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecInfo.

  Module InstrumentMasterChangeMessage.

    (** Broadcasts a change to the instrument master *)
    Record t := {
      instrument_id : N;
      instrument_name : list byte;
      instrument_description : list byte;
      instrument_update_time : N;
      delete_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (instrument_description record) = 25 /\
      (instrument_update_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (delete_flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (instrument_id record) ++
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 25 (instrument_description record) ++
      encode_uint 4 (instrument_update_time record) ++
      encode_bytes 1 (delete_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (instrument_name_value, bytes) =>
              match decode_bytes 25 bytes with
              | None => None
              | Some (instrument_description_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instrument_update_time_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (delete_flag_value, bytes) =>
                          Some ({| instrument_id := instrument_id_value; instrument_name := instrument_name_value; instrument_description := instrument_description_value; instrument_update_time := instrument_update_time_value; delete_flag := delete_flag_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentMasterChangeMessage.

  Module ParticipantMasterChangeMessage.

    (** Broadcasts a change to the participant master *)
    Record t := {
      participant_id : list byte;
      participant_name : list byte;
      participant_status : list byte;
      participant_update_date_time : N;
      delete_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 12 /\
      Datatypes.length (participant_name record) = 25 /\
      Datatypes.length (participant_status record) = 1 /\
      (participant_update_date_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (delete_flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (participant_id record) ++
      encode_bytes 25 (participant_name record) ++
      encode_bytes 1 (participant_status record) ++
      encode_uint 4 (participant_update_date_time record) ++
      encode_bytes 1 (delete_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match decode_bytes 25 bytes with
          | None => None
          | Some (participant_name_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (participant_status_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (participant_update_date_time_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (delete_flag_value, bytes) =>
                          Some ({| participant_id := participant_id_value; participant_name := participant_name_value; participant_status := participant_status_value; participant_update_date_time := participant_update_date_time_value; delete_flag := delete_flag_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ParticipantMasterChangeMessage.

  Module SecInfo2.

    (** SEC_INFO *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      series : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (series_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (expiry_date_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (strike_price_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (option_type_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ca_level_value, bytes) =>
                                  Some ({| instrument_name := instrument_name_value; symbol := symbol_value; series := series_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecInfo2.

  Module TurnoverLimitExceededBody.

    (** Turnover Limit Exceeded Body *)
    Record t := {
      broker_code : list byte;
      counter_broker_code : list byte;
      warning_type : N;
      token : N;
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
      trade_number : N;
      trade_price : N;
      trade_volume : N;
      final : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (broker_code record) = 5 /\
      Datatypes.length (counter_broker_code record) = 5 /\
      (warning_type record < 256 ^ N.of_nat 2)%N /\
      (token record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (final record) = 1 /\
      Datatypes.length (filler record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (broker_code record) ++
      encode_bytes 5 (counter_broker_code record) ++
      encode_uint 2 (warning_type record) ++
      encode_uint 4 (token record) ++
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 4 (trade_volume record) ++
      encode_bytes 1 (final record) ++
      encode_bytes 1 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (broker_code_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (counter_broker_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (warning_type_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (token_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (instrument_name_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (expiry_date_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (strike_price_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (option_type_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (ca_level_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (trade_number_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (trade_price_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (trade_volume_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (final_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (filler_value, bytes) =>
                                                                  Some ({| broker_code := broker_code_value; counter_broker_code := counter_broker_code_value; warning_type := warning_type_value; token := token_value; instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value; trade_number := trade_number_value; trade_price := trade_price_value; trade_volume := trade_volume_value; final := final_value; filler := filler_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 58.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TurnoverLimitExceededBody.

  Module SecInfo3.

    (** SEC_INFO *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      series : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (series_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (expiry_date_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (strike_price_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (option_type_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ca_level_value, bytes) =>
                                  Some ({| instrument_name := instrument_name_value; symbol := symbol_value; series := series_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecInfo3.

End NseFoBroadcastV950.
