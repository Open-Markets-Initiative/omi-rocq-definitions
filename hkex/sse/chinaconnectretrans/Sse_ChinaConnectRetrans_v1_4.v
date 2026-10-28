From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Hong Kong Exchanges and Clearing Orion Market Data China Connect Retransmission

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

Module SseChinaConnectRetransV14.

  Module PacketHeader.

    (** Omd packet header (byte-identical to the Udp form; SeqNum and SendTime set to 0 on Tcp per §3.5) *)
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

    (** The Sequence Reset message is sent on each multicast channel at start of day. The client must ignore the sequence number of the Sequence Reset message itself, and set the next expected sequence number to NewSeqNo. On receipt clients must clear all cached data for all eligible instruments traded in SSE and SZSE and then subscribe to the refresh channels. *)
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

    (** The Disaster Recovery (DR) Signal message is sent on a dedicated multicast channel whenever site failover is triggered. *)
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

  Module MarketDefinitionMessage.

    (** The Market Definition message is generated at the start of the business day for each market (SSE or SZSE). Market Definition messages for different markets are sent via different channels. *)
    Record t := {
      market_code : list byte;
      market_name : list byte;
      currency_code : list byte;
      number_of_securities : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_code record) = 4 /\
      Datatypes.length (market_name record) = 25 /\
      Datatypes.length (currency_code record) = 3 /\
      (number_of_securities record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (market_code record) ++
      encode_bytes 25 (market_name record) ++
      encode_bytes 3 (currency_code record) ++
      encode_uint 4 (number_of_securities record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (market_code_value, bytes) =>
          match decode_bytes 25 bytes with
          | None => None
          | Some (market_name_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (currency_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (number_of_securities_value, bytes) =>
                      Some ({| market_code := market_code_value; market_name := market_name_value; currency_code := currency_code_value; number_of_securities := number_of_securities_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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

  End MarketDefinitionMessage.

  Module LogonMessage.

    (** The Logon message enables client authentication. Not required for multicast channels; only used for retransmission requests. Client sends Logon containing username to OMD-CC which responds with Logon Response. *)
    Record t := {
      username : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (username record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (username_value, bytes) =>
          Some ({| username := username_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End LogonMessage.

  Module LogonResponseMessage.

    (** Response to a Logon request indicating session status. *)
    Record t := {
      session_status : N;
      filler_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_status record < 256 ^ N.of_nat 1)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (session_status record) ++
      encode_uint 3 (filler_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (session_status_value, bytes) =>
          match decode_uint 3 bytes with
          | None => None
          | Some (filler_3_value, bytes) =>
              Some ({| session_status := session_status_value; filler_3 := filler_3_value |}, bytes)
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

  End LogonResponseMessage.

  Module RetransmissionRequestMessage.

    (** Client-initiated request to retransmit a range of messages from a specific multicast channel. *)
    Record t := {
      channel_id : N;
      filler_2 : N;
      begin_seq_num : N;
      end_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_id record < 256 ^ N.of_nat 2)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N /\
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_id record) ++
      encode_uint 2 (filler_2 record) ++
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (filler_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (begin_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (end_seq_num_value, bytes) =>
                      Some ({| channel_id := channel_id_value; filler_2 := filler_2_value; begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End RetransmissionRequestMessage.

  Module RetransmissionResponseMessage.

    (** Server response to a Retransmission Request indicating whether the range can be resent. *)
    Record t := {
      channel_id : N;
      retrans_status : N;
      filler_1 : N;
      begin_seq_num : N;
      end_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_id record < 256 ^ N.of_nat 2)%N /\
      (retrans_status record < 256 ^ N.of_nat 1)%N /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_id record) ++
      encode_uint 1 (retrans_status record) ++
      encode_uint 1 (filler_1 record) ++
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (retrans_status_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (filler_1_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (begin_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (end_seq_num_value, bytes) =>
                          Some ({| channel_id := channel_id_value; retrans_status := retrans_status_value; filler_1 := filler_1_value; begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End RetransmissionResponseMessage.

  Module SecurityDefinitionMessage.

    (** The Security Definition message contains all the reference data for a security. Security Definition messages for different markets (SSE and SZSE) are sent via different channels. *)
    Record t := {
      security_code : N;
      market_code : list byte;
      isin_code : list byte;
      instrument_type : list byte;
      filler_2 : N;
      security_short_name : list byte;
      currency_code : list byte;
      filler_60 : list byte;
      security_name_gb : list byte;
      lot_size : N;
      previous_closing_price : N;
      filler_1 : N;
      shortsell_flag : list byte;
      filler_6 : N;
      listing_date : N;
      filler_7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_code record) = 4 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (instrument_type record) = 4 /\
      (filler_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (security_short_name record) = 40 /\
      Datatypes.length (currency_code record) = 3 /\
      Datatypes.length (filler_60 record) = 60 /\
      Datatypes.length (security_name_gb record) = 60 /\
      (lot_size record < 256 ^ N.of_nat 4)%N /\
      (previous_closing_price record < 256 ^ N.of_nat 4)%N /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (shortsell_flag record) = 1 /\
      (filler_6 record < 256 ^ N.of_nat 6)%N /\
      (listing_date record < 256 ^ N.of_nat 4)%N /\
      (filler_7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_bytes 4 (market_code record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 4 (instrument_type record) ++
      encode_uint 2 (filler_2 record) ++
      encode_bytes 40 (security_short_name record) ++
      encode_bytes 3 (currency_code record) ++
      encode_bytes 60 (filler_60 record) ++
      encode_bytes 60 (security_name_gb record) ++
      encode_uint 4 (lot_size record) ++
      encode_uint 4 (previous_closing_price record) ++
      encode_uint 1 (filler_1 record) ++
      encode_bytes 1 (shortsell_flag record) ++
      encode_uint 6 (filler_6 record) ++
      encode_uint 4 (listing_date record) ++
      encode_uint 7 (filler_7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_code_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (instrument_type_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (filler_2_value, bytes) =>
                          match decode_bytes 40 bytes with
                          | None => None
                          | Some (security_short_name_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (currency_code_value, bytes) =>
                                  match decode_bytes 60 bytes with
                                  | None => None
                                  | Some (filler_60_value, bytes) =>
                                      match decode_bytes 60 bytes with
                                      | None => None
                                      | Some (security_name_gb_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (lot_size_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (previous_closing_price_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (filler_1_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (shortsell_flag_value, bytes) =>
                                                          match decode_uint 6 bytes with
                                                          | None => None
                                                          | Some (filler_6_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (listing_date_value, bytes) =>
                                                                  match decode_uint 7 bytes with
                                                                  | None => None
                                                                  | Some (filler_7_value, bytes) =>
                                                                      Some ({| security_code := security_code_value; market_code := market_code_value; isin_code := isin_code_value; instrument_type := instrument_type_value; filler_2 := filler_2_value; security_short_name := security_short_name_value; currency_code := currency_code_value; filler_60 := filler_60_value; security_name_gb := security_name_gb_value; lot_size := lot_size_value; previous_closing_price := previous_closing_price_value; filler_1 := filler_1_value; shortsell_flag := shortsell_flag_value; filler_6 := filler_6_value; listing_date := listing_date_value; filler_7 := filler_7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 216.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityDefinitionMessage.

  Module SecurityStatusMessage.

    (** The Security Status message is generated at the start of the business day if the security is halted, and whenever a security state or trading phase changes. Security Status messages for different markets (SSE and SZSE) are sent via different channels. *)
    Record t := {
      security_code : N;
      security_trading_status : N;
      filler_3 : N;
      trading_phase_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (security_trading_status record < 256 ^ N.of_nat 1)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N /\
      Datatypes.length (trading_phase_code record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 1 (security_trading_status record) ++
      encode_uint 3 (filler_3 record) ++
      encode_bytes 8 (trading_phase_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (security_trading_status_value, bytes) =>
              match decode_uint 3 bytes with
              | None => None
              | Some (filler_3_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trading_phase_code_value, bytes) =>
                      Some ({| security_code := security_code_value; security_trading_status := security_trading_status_value; filler_3 := filler_3_value; trading_phase_code := trading_phase_code_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End SecurityStatusMessage.

  Module StatisticsMessage.

    (** The Statistics message provides statistics including turnover. Statistics messages for different markets (SSE and SZSE) are sent via different channels. *)
    Record t := {
      security_code : N;
      shares_traded : N;
      turnover : N;
      high_price : N;
      low_price : N;
      last_price : N;
      opening_price : N;
      filler_12 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (shares_traded record < 256 ^ N.of_nat 8)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 4)%N /\
      (low_price record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 4)%N /\
      (opening_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (filler_12 record) = 12.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 8 (shares_traded record) ++
      encode_uint 8 (turnover record) ++
      encode_uint 4 (high_price record) ++
      encode_uint 4 (low_price record) ++
      encode_uint 4 (last_price record) ++
      encode_uint 4 (opening_price record) ++
      encode_bytes 12 (filler_12 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (shares_traded_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (turnover_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (high_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (low_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (last_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (opening_price_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (filler_12_value, bytes) =>
                                      Some ({| security_code := security_code_value; shares_traded := shares_traded_value; turnover := turnover_value; high_price := high_price_value; low_price := low_price_value; last_price := last_price_value; opening_price := opening_price_value; filler_12 := filler_12_value |}, bytes)
                                  end
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StatisticsMessage.

  Module TopOfBookMessage.

    (** The Top Of Book (TOB) message is generated when the top price level has been modified. TOB messages for different markets (SSE and SZSE) are sent via different channels. *)
    Record t := {
      security_code : N;
      aggregate_bid_quantity : N;
      aggregate_ask_quantity : N;
      bid_price : N;
      ask_price : N;
      filler_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (aggregate_bid_quantity record < 256 ^ N.of_nat 8)%N /\
      (aggregate_ask_quantity record < 256 ^ N.of_nat 8)%N /\
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 4)%N /\
      (filler_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 8 (aggregate_bid_quantity record) ++
      encode_uint 8 (aggregate_ask_quantity record) ++
      encode_uint 4 (bid_price record) ++
      encode_uint 4 (ask_price record) ++
      encode_uint 8 (filler_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (aggregate_bid_quantity_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (aggregate_ask_quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (bid_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ask_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (filler_8_value, bytes) =>
                              Some ({| security_code := security_code_value; aggregate_bid_quantity := aggregate_bid_quantity_value; aggregate_ask_quantity := aggregate_ask_quantity_value; bid_price := bid_price_value; ask_price := ask_price_value; filler_8 := filler_8_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TopOfBookMessage.

End SseChinaConnectRetransV14.
