From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Hong Kong Exchanges and Clearing Orion Market Data Cash Index

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
  *)

Module HkexSecuritiesIndexV144.

  Module PacketHeader.

    (** Omd packet header (no payload compression; byte 3 is Filler) *)
    Record t := {
      pkt_size : N;
      msg_count : N;
      filler : N;
      seq_num : N;
      send_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (pkt_size record < 256 ^ N.of_nat 2)%N /\
      (msg_count record < 256 ^ N.of_nat 1)%N /\
      (filler record < 256 ^ N.of_nat 1)%N /\
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      (send_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (pkt_size record) ++
      encode_uint 1 (msg_count record) ++
      encode_uint 1 (filler record) ++
      encode_uint 4 (seq_num record) ++
      encode_uint 8 (send_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (pkt_size_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (msg_count_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (filler_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (send_time_value, bytes) =>
                          Some ({| pkt_size := pkt_size_value; msg_count := msg_count_value; filler := filler_value; seq_num := seq_num_value; send_time := send_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End PacketHeader.

  Module MsgHeader.

    (** Omd message header *)
    Record t := {
      msg_size : N;
      msg_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_size record < 256 ^ N.of_nat 2)%N /\
      (msg_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_size record) ++
      encode_uint 2 (msg_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_size_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              Some ({| msg_size := msg_size_value; msg_type := msg_type_value |}, bytes)
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

  End MsgHeader.

  Module SequenceResetMessage.

    (** The Sequence Reset message is sent on each multicast channel at start of day. It may also be sent when there is a need for the rectification of stock reference data before market open. *)
    Record t := {
      new_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (new_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (new_seq_no_value, bytes) =>
          Some ({| new_seq_no := new_seq_no_value |}, bytes)
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

  End SequenceResetMessage.

  Module DisasterRecoverySignalMessage.

    (** The Disaster Recovery (DR) Signal message is sent on a dedicated multicast channel whenever a site failover scenario is triggered. *)
    Record t := {
      dr_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (dr_status record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (dr_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (dr_status_value, bytes) =>
          Some ({| dr_status := dr_status_value |}, bytes)
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

  End DisasterRecoverySignalMessage.

  Module IndexDefinitionMessage.

    (** The Index Definition message contains the static referential data for the given index and is generated at the start of the business day. May be re-disseminated during trading hours. *)
    Record t := {
      index_code : list byte;
      index_source : list byte;
      currency_code : list byte;
      filler_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (index_code record) = 11 /\
      Datatypes.length (index_source record) = 1 /\
      Datatypes.length (currency_code record) = 3 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (index_code record) ++
      encode_bytes 1 (index_source record) ++
      encode_bytes 3 (currency_code record) ++
      encode_uint 1 (filler_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (index_code_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (index_source_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (currency_code_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (filler_1_value, bytes) =>
                      Some ({| index_code := index_code_value; index_source := index_source_value; currency_code := currency_code_value; filler_1 := filler_1_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexDefinitionMessage.

  Module IndexDataMessage.

    (** The Index Data message contains all the real-time data for a given index. Fields may be populated with null values to indicate when an update is not provided. *)
    Record t := {
      index_code : list byte;
      index_status : list byte;
      index_time : N;
      index_value : N;
      net_chg_prev_day : N;
      high_value : N;
      low_value : N;
      eas_value : N;
      index_turnover : N;
      opening_value : N;
      closing_value : N;
      previous_ses_close : N;
      index_volume : N;
      net_chg_prev_day_pct : N;
      exception : list byte;
      filler_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (index_code record) = 11 /\
      Datatypes.length (index_status record) = 1 /\
      (index_time record < 256 ^ N.of_nat 8)%N /\
      (index_value record < 256 ^ N.of_nat 8)%N /\
      (net_chg_prev_day record < 256 ^ N.of_nat 8)%N /\
      (high_value record < 256 ^ N.of_nat 8)%N /\
      (low_value record < 256 ^ N.of_nat 8)%N /\
      (eas_value record < 256 ^ N.of_nat 8)%N /\
      (index_turnover record < 256 ^ N.of_nat 8)%N /\
      (opening_value record < 256 ^ N.of_nat 8)%N /\
      (closing_value record < 256 ^ N.of_nat 8)%N /\
      (previous_ses_close record < 256 ^ N.of_nat 8)%N /\
      (index_volume record < 256 ^ N.of_nat 8)%N /\
      (net_chg_prev_day_pct record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exception record) = 1 /\
      (filler_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (index_code record) ++
      encode_bytes 1 (index_status record) ++
      encode_uint 8 (index_time record) ++
      encode_uint 8 (index_value record) ++
      encode_uint 8 (net_chg_prev_day record) ++
      encode_uint 8 (high_value record) ++
      encode_uint 8 (low_value record) ++
      encode_uint 8 (eas_value record) ++
      encode_uint 8 (index_turnover record) ++
      encode_uint 8 (opening_value record) ++
      encode_uint 8 (closing_value record) ++
      encode_uint 8 (previous_ses_close record) ++
      encode_uint 8 (index_volume record) ++
      encode_uint 4 (net_chg_prev_day_pct record) ++
      encode_bytes 1 (exception record) ++
      encode_uint 3 (filler_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (index_code_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (index_status_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (index_time_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (index_value_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (net_chg_prev_day_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (high_value_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (low_value_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (eas_value_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (index_turnover_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (opening_value_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (closing_value_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (previous_ses_close_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (index_volume_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (net_chg_prev_day_pct_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (exception_value, bytes) =>
                                                                  match decode_uint 3 bytes with
                                                                  | None => None
                                                                  | Some (filler_3_value, bytes) =>
                                                                      Some ({| index_code := index_code_value; index_status := index_status_value; index_time := index_time_value; index_value := index_value_value; net_chg_prev_day := net_chg_prev_day_value; high_value := high_value_value; low_value := low_value_value; eas_value := eas_value_value; index_turnover := index_turnover_value; opening_value := opening_value_value; closing_value := closing_value_value; previous_ses_close := previous_ses_close_value; index_volume := index_volume_value; net_chg_prev_day_pct := net_chg_prev_day_pct_value; exception := exception_value; filler_3 := filler_3_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 108.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexDataMessage.

End HkexSecuritiesIndexV144.
