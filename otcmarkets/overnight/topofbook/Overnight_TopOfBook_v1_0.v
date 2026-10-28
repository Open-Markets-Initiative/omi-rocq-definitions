From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * OTC Markets Group OTC Top of Book

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
      - a Composite rule
      - a run counted by a field
      - a field read in bits
  *)

Module OvernightTopOfBookV10.

  Module MessageHeader.

    (** Otc Udp Message Header *)
    Record t := {
      message_size : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_size record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_size record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_size_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_size := message_size_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  Module StartOfSpinMessage.

    (** After a Spin Response Message, with status 'S', this message appears on all channels and indicates the beginning of a spin message cycle. *)
    Record t := {
      spin_type : N;
      spin_start_time_milli : N;
      spin_last_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (spin_type record < 256 ^ N.of_nat 1)%N /\
      (spin_start_time_milli record < 256 ^ N.of_nat 8)%N /\
      (spin_last_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (spin_type record) ++
      encode_uint 8 (spin_start_time_milli record) ++
      encode_uint 4 (spin_last_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (spin_type_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (spin_start_time_milli_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (spin_last_seq_num_value, bytes) =>
                  Some ({| spin_type := spin_type_value; spin_start_time_milli := spin_start_time_milli_value; spin_last_seq_num := spin_last_seq_num_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End StartOfSpinMessage.

  Module EndOfSpinMessage.

    (** This message appears on all channels and indicates the end of a spin message cycle. It will be followed by a Spin Response Message, with status 'E'. *)
    Record t := {
      spin_type : N;
      spin_msg_ct : N;
      spin_end_time_milli : N;
      spin_last_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (spin_type record < 256 ^ N.of_nat 1)%N /\
      (spin_msg_ct record < 256 ^ N.of_nat 4)%N /\
      (spin_end_time_milli record < 256 ^ N.of_nat 8)%N /\
      (spin_last_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (spin_type record) ++
      encode_uint 4 (spin_msg_ct record) ++
      encode_uint 8 (spin_end_time_milli record) ++
      encode_uint 4 (spin_last_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (spin_type_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (spin_msg_ct_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (spin_end_time_milli_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (spin_last_seq_num_value, bytes) =>
                      Some ({| spin_type := spin_type_value; spin_msg_ct := spin_msg_ct_value; spin_end_time_milli := spin_end_time_milli_value; spin_last_seq_num := spin_last_seq_num_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End EndOfSpinMessage.

  Module TradingSessionMessage.

    (** This message appears on all channels and is sent out at the start of each Overnight OTC IDQS trading session: Order Acceptance at 7:00 PM, Market Open at 8:00 PM, Market Close at 7:45 AM. The message can also be sent mid-day if a technical outage caused a temporary closure of the market. *)
    Record t := {
      session_time : N;
      trading_session : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_time record < 256 ^ N.of_nat 8)%N /\
      (trading_session record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (session_time record) ++
      encode_uint 1 (trading_session record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (session_time_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (trading_session_value, bytes) =>
              Some ({| session_time := session_time_value; trading_session := trading_session_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TradingSessionMessage.

  Module TopOfBookMessage.

    (** This message appears on the TOB channel. Provides best bid and offer aggregated top-of-book. *)
    Record t := {
      time : N;
      symbol : list byte;
      ask_price : N;
      ask_volume : N;
      bid_price : N;
      bid_volume : N;
      unsolicited : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 14 /\
      (ask_price record < 256 ^ N.of_nat 8)%N /\
      (ask_volume record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 8)%N /\
      (bid_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (unsolicited record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time record) ++
      encode_bytes 14 (symbol record) ++
      encode_uint 8 (ask_price record) ++
      encode_uint 4 (ask_volume record) ++
      encode_uint 8 (bid_price record) ++
      encode_uint 4 (bid_volume record) ++
      encode_bytes 1 (unsolicited record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (ask_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ask_volume_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (bid_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (bid_volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (unsolicited_value, bytes) =>
                                  Some ({| time := time_value; symbol := symbol_value; ask_price := ask_price_value; ask_volume := ask_volume_value; bid_price := bid_price_value; bid_volume := bid_volume_value; unsolicited := unsolicited_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TopOfBookMessage.

  Module ImbalanceMessage.

    (** This message appears on all channels. This message is not available in the Overnight TradingSession. *)
    Record t := {
      time : N;
      symbol : list byte;
      current_inside_paired_shares : N;
      current_inside_closing_price : N;
      current_inside_imbalance_quantity : N;
      current_inside_imbalance_side : list byte;
      full_closing_price : N;
      ocio_only_closing_price : N;
      moc_shares_unmatched : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 14 /\
      (current_inside_paired_shares record < 256 ^ N.of_nat 4)%N /\
      (current_inside_closing_price record < 256 ^ N.of_nat 8)%N /\
      (current_inside_imbalance_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (current_inside_imbalance_side record) = 1 /\
      (full_closing_price record < 256 ^ N.of_nat 8)%N /\
      (ocio_only_closing_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (moc_shares_unmatched record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time record) ++
      encode_bytes 14 (symbol record) ++
      encode_uint 4 (current_inside_paired_shares record) ++
      encode_uint 8 (current_inside_closing_price record) ++
      encode_uint 4 (current_inside_imbalance_quantity record) ++
      encode_bytes 1 (current_inside_imbalance_side record) ++
      encode_uint 8 (full_closing_price record) ++
      encode_uint 8 (ocio_only_closing_price record) ++
      encode_bytes 1 (moc_shares_unmatched record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (current_inside_paired_shares_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (current_inside_closing_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (current_inside_imbalance_quantity_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (current_inside_imbalance_side_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (full_closing_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (ocio_only_closing_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (moc_shares_unmatched_value, bytes) =>
                                          Some ({| time := time_value; symbol := symbol_value; current_inside_paired_shares := current_inside_paired_shares_value; current_inside_closing_price := current_inside_closing_price_value; current_inside_imbalance_quantity := current_inside_imbalance_quantity_value; current_inside_imbalance_side := current_inside_imbalance_side_value; full_closing_price := full_closing_price_value; ocio_only_closing_price := ocio_only_closing_price_value; moc_shares_unmatched := moc_shares_unmatched_value |}, bytes)
                                      end
                                  end
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ImbalanceMessage.

  Module SystemRecoveryEventMessage.

    (** In case of a catastrophic issue at the exchange, the system sends a System Recovery Event. The first event (type 'S') instructs clients to prepare and reset caches; clients must clean all cached state. A second event (type 'B') indicates recovery begins, after which the system performs a spin for all symbols and open orders. *)
    Record t := {
      deprecated : N;
      recovery_type : N;
      next_sequence_number : N;
      recovery_start_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (deprecated record < 256 ^ N.of_nat 4)%N /\
      (recovery_type record < 256 ^ N.of_nat 1)%N /\
      (next_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (recovery_start_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (deprecated record) ++
      encode_uint 1 (recovery_type record) ++
      encode_uint 4 (next_sequence_number record) ++
      encode_uint 8 (recovery_start_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (deprecated_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (recovery_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (next_sequence_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (recovery_start_time_value, bytes) =>
                      Some ({| deprecated := deprecated_value; recovery_type := recovery_type_value; next_sequence_number := next_sequence_number_value; recovery_start_time := recovery_start_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End SystemRecoveryEventMessage.

End OvernightTopOfBookV10.
