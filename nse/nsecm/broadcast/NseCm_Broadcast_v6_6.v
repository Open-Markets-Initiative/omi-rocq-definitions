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
  *)

Module NseCmBroadcastV66.

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

  Module ParticipantMasterChangeMessage.

    (** Sent whenever there is any participant change *)
    Record t := {
      participant_id : list byte;
      participant_name : list byte;
      participant_status : list byte;
      participant_update_date_time : N;
      delete_flag : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 12 /\
      Datatypes.length (participant_name record) = 25 /\
      Datatypes.length (participant_status record) = 1 /\
      (participant_update_date_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (delete_flag record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (participant_id record) ++
      encode_bytes 25 (participant_name record) ++
      encode_bytes 1 (participant_status record) ++
      encode_uint 4 (participant_update_date_time record) ++
      encode_bytes 1 (delete_flag record) ++
      encode_uint 1 (reserved_1 record).

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
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| participant_id := participant_id_value; participant_name := participant_name_value; participant_status := participant_status_value; participant_update_date_time := participant_update_date_time_value; delete_flag := delete_flag_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ParticipantMasterChangeMessage.

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

  Module TurnoverExceededMessage.

    (** Sent when a broker turnover is about to exceed or has already exceeded the limit, deactivating the broker *)
    Record t := {
      broker_code : list byte;
      counter_broker_code : list byte;
      warning_type : N;
      sec_info : SecInfo2.t;
      trade_number : N;
      trade_price : N;
      trade_volume : N;
      final : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (broker_code record) = 5 /\
      Datatypes.length (counter_broker_code record) = 5 /\
      (warning_type record < 256 ^ N.of_nat 2)%N /\
      SecInfo2.bounded (sec_info record) /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (final record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (broker_code record) ++
      encode_bytes 5 (counter_broker_code record) ++
      encode_uint 2 (warning_type record) ++
      SecInfo2.encode (sec_info record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 4 (trade_volume record) ++
      encode_bytes 1 (final record).

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
                  match SecInfo2.decode bytes with
                  | None => None
                  | Some (sec_info_value, bytes) =>
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
                                      Some ({| broker_code := broker_code_value; counter_broker_code := counter_broker_code_value; warning_type := warning_type_value; sec_info := sec_info_value; trade_number := trade_number_value; trade_price := trade_price_value; trade_volume := trade_volume_value; final := final_value |}, bytes)
                                  end
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !SecInfo2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite SecInfo2.decode_encode by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SecInfo2.eq_dec]. Defined.

  End TurnoverExceededMessage.

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

  Module BrokerReactivatedMessage.

    (** Sent when a broker is reactivated after being deactivated *)
    Record t := {
      broker_code : list byte;
      counter_broker_code : list byte;
      warning_type : N;
      sec_info : SecInfo3.t;
      trade_number : N;
      trade_price : N;
      trade_volume : N;
      final : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (broker_code record) = 5 /\
      Datatypes.length (counter_broker_code record) = 5 /\
      (warning_type record < 256 ^ N.of_nat 2)%N /\
      SecInfo3.bounded (sec_info record) /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (final record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (broker_code record) ++
      encode_bytes 5 (counter_broker_code record) ++
      encode_uint 2 (warning_type record) ++
      SecInfo3.encode (sec_info record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 4 (trade_volume record) ++
      encode_bytes 1 (final record).

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
                  match SecInfo3.decode bytes with
                  | None => None
                  | Some (sec_info_value, bytes) =>
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
                                      Some ({| broker_code := broker_code_value; counter_broker_code := counter_broker_code_value; warning_type := warning_type_value; sec_info := sec_info_value; trade_number := trade_number_value; trade_price := trade_price_value; trade_volume := trade_volume_value; final := final_value |}, bytes)
                                  end
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !SecInfo3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite SecInfo3.decode_encode by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SecInfo3.eq_dec]. Defined.

  End BrokerReactivatedMessage.

  Module StAuctionInqInfo.

    (** ST_AUCTION_INQ_INFO *)
    Record t := {
      token_long_4 : N;
      auction_number : N;
      auction_status_short_2 : N;
      initiator_type : N;
      total_buy_qty : N;
      best_buy_price : N;
      total_sell_qty : N;
      best_sell_price : N;
      auction_price : N;
      auction_qty : N;
      settlement_period : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (token_long_4 record < 256 ^ N.of_nat 4)%N /\
      (auction_number record < 256 ^ N.of_nat 2)%N /\
      (auction_status_short_2 record < 256 ^ N.of_nat 2)%N /\
      (initiator_type record < 256 ^ N.of_nat 2)%N /\
      (total_buy_qty record < 256 ^ N.of_nat 4)%N /\
      (best_buy_price record < 256 ^ N.of_nat 4)%N /\
      (total_sell_qty record < 256 ^ N.of_nat 4)%N /\
      (best_sell_price record < 256 ^ N.of_nat 4)%N /\
      (auction_price record < 256 ^ N.of_nat 4)%N /\
      (auction_qty record < 256 ^ N.of_nat 4)%N /\
      (settlement_period record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (token_long_4 record) ++
      encode_uint 2 (auction_number record) ++
      encode_uint 2 (auction_status_short_2 record) ++
      encode_uint 2 (initiator_type record) ++
      encode_uint 4 (total_buy_qty record) ++
      encode_uint 4 (best_buy_price record) ++
      encode_uint 4 (total_sell_qty record) ++
      encode_uint 4 (best_sell_price record) ++
      encode_uint 4 (auction_price record) ++
      encode_uint 4 (auction_qty record) ++
      encode_uint 2 (settlement_period record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (token_long_4_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (auction_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (auction_status_short_2_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (initiator_type_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (total_buy_qty_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (best_buy_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (total_sell_qty_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (best_sell_price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (auction_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (auction_qty_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (settlement_period_value, bytes) =>
                                                  Some ({| token_long_4 := token_long_4_value; auction_number := auction_number_value; auction_status_short_2 := auction_status_short_2_value; initiator_type := initiator_type_value; total_buy_qty := total_buy_qty_value; best_buy_price := best_buy_price_value; total_sell_qty := total_sell_qty_value; best_sell_price := best_sell_price_value; auction_price := auction_price_value; auction_qty := auction_qty_value; settlement_period := settlement_period_value |}, bytes)
                                              end
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
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End StAuctionInqInfo.

  Module AuctionInquiryMessage.

    (** Sent whenever there is any auction related activity, including a change in the auction market by order *)
    Record t := {
      st_auction_inq_info : StAuctionInqInfo.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      StAuctionInqInfo.bounded (st_auction_inq_info record).

    Definition encode (record : t) : list byte :=
      StAuctionInqInfo.encode (st_auction_inq_info record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match StAuctionInqInfo.decode bytes with
      | None => None
      | Some (st_auction_inq_info_value, bytes) =>
          Some ({| st_auction_inq_info := st_auction_inq_info_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !StAuctionInqInfo.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite StAuctionInqInfo.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply StAuctionInqInfo.eq_dec]. Defined.

  End AuctionInquiryMessage.

  Module SecInfo4.

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

  End SecInfo4.

  Module SecInfo5.

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

  End SecInfo5.

  Module SecInfo6.

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

  End SecInfo6.

  Module SecInfo7.

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

  End SecInfo7.

  Module SecInfo8.

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

  End SecInfo8.

  Module SecInfo9.

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

  End SecInfo9.

  Module SecInfo10.

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

  End SecInfo10.

  Module SecInfo11.

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

  End SecInfo11.

  Module SecInfo12.

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

  End SecInfo12.

  Module SecInfo13.

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

  End SecInfo13.

  Module SecInfo14.

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

  End SecInfo14.

  Module SecInfo15.

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

  End SecInfo15.

  Module SecInfo16.

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

  End SecInfo16.

  Module SecInfo17.

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

  End SecInfo17.

  Module SymbolStatusChangeActionMessage.

    (** Carries a security level trading or market status change *)
    Record t := {
      sec_info : SecInfo17.t;
      market_type : N;
      reserved_2 : N;
      action_code_short_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SecInfo17.bounded (sec_info record) /\
      (market_type record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      (action_code_short_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      SecInfo17.encode (sec_info record) ++
      encode_uint 2 (market_type record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_uint 2 (action_code_short_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SecInfo17.decode bytes with
      | None => None
      | Some (sec_info_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (market_type_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (reserved_2_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (action_code_short_2_value, bytes) =>
                      Some ({| sec_info := sec_info_value; market_type := market_type_value; reserved_2 := reserved_2_value; action_code_short_2 := action_code_short_2_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SecInfo17.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SecInfo17.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply SecInfo17.eq_dec]. Defined.

  End SymbolStatusChangeActionMessage.

  Module SecInfo18.

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

  End SecInfo18.

  Module SecurityOpenPriceMessage.

    (** Carries the open price of a security when the market opens. The document states this transaction code is not sent by the exchange *)
    Record t := {
      sec_info : SecInfo18.t;
      token_short_2 : N;
      opening_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SecInfo18.bounded (sec_info record) /\
      (token_short_2 record < 256 ^ N.of_nat 2)%N /\
      (opening_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      SecInfo18.encode (sec_info record) ++
      encode_uint 2 (token_short_2 record) ++
      encode_uint 4 (opening_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SecInfo18.decode bytes with
      | None => None
      | Some (sec_info_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (token_short_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (opening_price_value, bytes) =>
                  Some ({| sec_info := sec_info_value; token_short_2 := token_short_2_value; opening_price := opening_price_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SecInfo18.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SecInfo18.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply SecInfo18.eq_dec]. Defined.

  End SecurityOpenPriceMessage.

  Module SecInfo19.

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

  End SecInfo19.

End NseCmBroadcastV66.
