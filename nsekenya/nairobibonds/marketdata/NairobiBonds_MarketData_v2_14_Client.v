From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Nairobi Securities Exchange Nairobi Bonds Market Data

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
      - a run of a stated number of entries

    License: MIT No Attribution
  *)

Module NairobiBondsMarketDataV214Client.

  Module TransportHeader.

    (** Table 1: Transport Header *)
    Record t := {
      start_byte : N;
      message_length : N;
      length_check : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_byte record < 256 ^ N.of_nat 1)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (length_check record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (start_byte record) ++
      encode_uint_le 2 (message_length record) ++
      encode_uint 1 (length_check record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (start_byte_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (message_length_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (length_check_value, bytes) =>
                  Some ({| start_byte := start_byte_value; message_length := message_length_value; length_check := length_check_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TransportHeader.

  Module UserName.

    (** User name as assigned by the exchange *)
    Record t := {
      user_name_length_byte : N;
      user_name_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_name_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user_name_characters record) = 15.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (user_name_length_byte record) ++
      encode_bytes 15 (user_name_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (user_name_length_byte_value, bytes) =>
          match decode_bytes 15 bytes with
          | None => None
          | Some (user_name_characters_value, bytes) =>
              Some ({| user_name_length_byte := user_name_length_byte_value; user_name_characters := user_name_characters_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UserName.

  Module Time.

    (** Time *)
    Record t := {
      hours : N;
      minutes : N;
      seconds : N;
      unused_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (hours record < 256 ^ N.of_nat 1)%N /\
      (minutes record < 256 ^ N.of_nat 1)%N /\
      (seconds record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (unused_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (hours record) ++
      encode_uint 1 (minutes record) ++
      encode_uint 1 (seconds record) ++
      encode_bytes 1 (unused_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (hours_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (minutes_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (seconds_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (unused_1_value, bytes) =>
                      Some ({| hours := hours_value; minutes := minutes_value; seconds := seconds_value; unused_1 := unused_1_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End Time.

  Module ClientMessageHeader.

    (** Table 2: Message Header *)
    Record t := {
      sequence_number : N;
      user_name : UserName.t;
      user_number : N;
      time : Time.t;
      client_message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      UserName.bounded (user_name record) /\
      (user_number record < 256 ^ N.of_nat 4)%N /\
      Time.bounded (time record) /\
      (client_message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (sequence_number record) ++
      UserName.encode (user_name record) ++
      encode_uint_le 4 (user_number record) ++
      Time.encode (time record) ++
      encode_uint 1 (client_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match UserName.decode bytes with
          | None => None
          | Some (user_name_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (user_number_value, bytes) =>
                  match Time.decode bytes with
                  | None => None
                  | Some (time_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (client_message_type_value, bytes) =>
                          Some ({| sequence_number := sequence_number_value; user_name := user_name_value; user_number := user_number_value; time := time_value; client_message_type := client_message_type_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !UserName.encode_length, !Time.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite UserName.decode_encode by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite Time.decode_encode by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply UserName.eq_dec | apply Time.eq_dec]. Defined.

  End ClientMessageHeader.

  Module LogInMessage.

    (** Log in message. *)
    Record t := {
      encrypted_password : list byte;
      new_password : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (encrypted_password record) = 312 /\
      Datatypes.length (new_password record) = 312.

    Definition encode (record : t) : list byte :=
      encode_bytes 312 (encrypted_password record) ++
      encode_bytes 312 (new_password record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 312 bytes with
      | None => None
      | Some (encrypted_password_value, bytes) =>
          match decode_bytes 312 bytes with
          | None => None
          | Some (new_password_value, bytes) =>
              Some ({| encrypted_password := encrypted_password_value; new_password := new_password_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 624.
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

  End LogInMessage.

  Module ReRequestMessage.

    (** Re-Request of 59 messages. *)
    Record t := {
      from_sequence : N;
      to_sequence : N;
      market_shard_number_i_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (from_sequence record < 256 ^ N.of_nat 4)%N /\
      (to_sequence record < 256 ^ N.of_nat 4)%N /\
      (market_shard_number_i_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (from_sequence record) ++
      encode_uint_le 4 (to_sequence record) ++
      encode_uint_le 4 (market_shard_number_i_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (from_sequence_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (to_sequence_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (market_shard_number_i_4_value, bytes) =>
                  Some ({| from_sequence := from_sequence_value; to_sequence := to_sequence_value; market_shard_number_i_4 := market_shard_number_i_4_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ReRequestMessage.

  Module DownloadDate.

    (** Download Date *)
    Record t := {
      year : N;
      month : N;
      day : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (year record < 256 ^ N.of_nat 4)%N /\
      (month record < 256 ^ N.of_nat 4)%N /\
      (day record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (year record) ++
      encode_uint_le 4 (month record) ++
      encode_uint_le 4 (day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  Some ({| year := year_value; month := month_value; day := day_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End DownloadDate.

  Module RequestDataRetrievalMessage.

    (** Allows users to request data from the system. *)
    Record t := {
      data_type : N;
      unused_1 : list byte;
      last_piece_of_chunk : N;
      re_request : N;
      action : N;
      specific_record : N;
      download_date : DownloadDate.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (data_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (unused_1 record) = 1 /\
      (last_piece_of_chunk record < 256 ^ N.of_nat 1)%N /\
      (re_request record < 256 ^ N.of_nat 1)%N /\
      (action record < 256 ^ N.of_nat 4)%N /\
      (specific_record record < 256 ^ N.of_nat 4)%N /\
      DownloadDate.bounded (download_date record).

    Definition encode (record : t) : list byte :=
      encode_uint 1 (data_type record) ++
      encode_bytes 1 (unused_1 record) ++
      encode_uint 1 (last_piece_of_chunk record) ++
      encode_uint 1 (re_request record) ++
      encode_uint_le 4 (action record) ++
      encode_uint_le 4 (specific_record record) ++
      DownloadDate.encode (download_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (data_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (unused_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (last_piece_of_chunk_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (re_request_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (action_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (specific_record_value, bytes) =>
                              match DownloadDate.decode bytes with
                              | None => None
                              | Some (download_date_value, bytes) =>
                                  Some ({| data_type := data_type_value; unused_1 := unused_1_value; last_piece_of_chunk := last_piece_of_chunk_value; re_request := re_request_value; action := action_value; specific_record := specific_record_value; download_date := download_date_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !encode_uint_le_length, !DownloadDate.encode_length. reflexivity.
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
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite DownloadDate.decode_encode by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply DownloadDate.eq_dec]. Defined.

  End RequestDataRetrievalMessage.

  Module Date.

    (** Date *)
    Record t := {
      year : N;
      month : N;
      day : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (year record < 256 ^ N.of_nat 4)%N /\
      (month record < 256 ^ N.of_nat 4)%N /\
      (day record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (year record) ++
      encode_uint_le 4 (month record) ++
      encode_uint_le 4 (day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  Some ({| year := year_value; month := month_value; day := day_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Date.

  Module InstrumentNameP5.

    (** Defines the instrument which represents this contract. *)
    Record t := {
      instrument_name_p_5_length_byte : N;
      instrument_name_p_5_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_name_p_5_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (instrument_name_p_5_characters record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_name_p_5_length_byte record) ++
      encode_bytes 4 (instrument_name_p_5_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_name_p_5_length_byte_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_name_p_5_characters_value, bytes) =>
              Some ({| instrument_name_p_5_length_byte := instrument_name_p_5_length_byte_value; instrument_name_p_5_characters := instrument_name_p_5_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End InstrumentNameP5.

  Module SecondaryDate.

    (** Secondary Date *)
    Record t := {
      year : N;
      month : N;
      day : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (year record < 256 ^ N.of_nat 4)%N /\
      (month record < 256 ^ N.of_nat 4)%N /\
      (day record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (year record) ++
      encode_uint_le 4 (month record) ++
      encode_uint_le 4 (day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  Some ({| year := year_value; month := month_value; day := day_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SecondaryDate.

  Module SecondaryInstrumentNameP5.

    (** For strategy type products such as Product spreads, represents the instrument name of the second leg of the contract. *)
    Record t := {
      secondary_instrument_name_p_5_length_byte : N;
      secondary_instrument_name_p_5_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (secondary_instrument_name_p_5_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (secondary_instrument_name_p_5_characters record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (secondary_instrument_name_p_5_length_byte record) ++
      encode_bytes 4 (secondary_instrument_name_p_5_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (secondary_instrument_name_p_5_length_byte_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (secondary_instrument_name_p_5_characters_value, bytes) =>
              Some ({| secondary_instrument_name_p_5_length_byte := secondary_instrument_name_p_5_length_byte_value; secondary_instrument_name_p_5_characters := secondary_instrument_name_p_5_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End SecondaryInstrumentNameP5.

  Module Contract.

    (** Contract *)
    Record t := {
      identifier_prefix_i_4 : N;
      date : Date.t;
      instrument_name_p_5 : InstrumentNameP5.t;
      strike : N;
      call_put_c_1 : list byte;
      secondary_date : SecondaryDate.t;
      secondary_instrument_name_p_5 : SecondaryInstrumentNameP5.t;
      is_delta_option : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (identifier_prefix_i_4 record < 256 ^ N.of_nat 4)%N /\
      Date.bounded (date record) /\
      InstrumentNameP5.bounded (instrument_name_p_5 record) /\
      (strike record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (call_put_c_1 record) = 1 /\
      SecondaryDate.bounded (secondary_date record) /\
      SecondaryInstrumentNameP5.bounded (secondary_instrument_name_p_5 record) /\
      (is_delta_option record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (identifier_prefix_i_4 record) ++
      Date.encode (date record) ++
      InstrumentNameP5.encode (instrument_name_p_5 record) ++
      encode_uint_le 8 (strike record) ++
      encode_bytes 1 (call_put_c_1 record) ++
      SecondaryDate.encode (secondary_date record) ++
      SecondaryInstrumentNameP5.encode (secondary_instrument_name_p_5 record) ++
      encode_uint 1 (is_delta_option record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (identifier_prefix_i_4_value, bytes) =>
          match Date.decode bytes with
          | None => None
          | Some (date_value, bytes) =>
              match InstrumentNameP5.decode bytes with
              | None => None
              | Some (instrument_name_p_5_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (strike_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (call_put_c_1_value, bytes) =>
                          match SecondaryDate.decode bytes with
                          | None => None
                          | Some (secondary_date_value, bytes) =>
                              match SecondaryInstrumentNameP5.decode bytes with
                              | None => None
                              | Some (secondary_instrument_name_p_5_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (is_delta_option_value, bytes) =>
                                      Some ({| identifier_prefix_i_4 := identifier_prefix_i_4_value; date := date_value; instrument_name_p_5 := instrument_name_p_5_value; strike := strike_value; call_put_c_1 := call_put_c_1_value; secondary_date := secondary_date_value; secondary_instrument_name_p_5 := secondary_instrument_name_p_5_value; is_delta_option := is_delta_option_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !Date.encode_length, !InstrumentNameP5.encode_length, !encode_bytes_length, !SecondaryDate.encode_length, !SecondaryInstrumentNameP5.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite Date.decode_encode by exact bound_1.
      rewrite InstrumentNameP5.decode_encode by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite SecondaryDate.decode_encode by exact bound_5.
      rewrite SecondaryInstrumentNameP5.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Date.eq_dec | apply InstrumentNameP5.eq_dec | apply SecondaryDate.eq_dec | apply SecondaryInstrumentNameP5.eq_dec]. Defined.

  End Contract.

  Module ContractName.

    (** Contract Name *)
    Record t := {
      identifier_prefix_i_4 : N;
      date : Date.t;
      instrument_name_p_5 : InstrumentNameP5.t;
      strike : N;
      call_put_c_1 : list byte;
      secondary_date : SecondaryDate.t;
      secondary_instrument_name_p_5 : SecondaryInstrumentNameP5.t;
      is_delta_option : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (identifier_prefix_i_4 record < 256 ^ N.of_nat 4)%N /\
      Date.bounded (date record) /\
      InstrumentNameP5.bounded (instrument_name_p_5 record) /\
      (strike record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (call_put_c_1 record) = 1 /\
      SecondaryDate.bounded (secondary_date record) /\
      SecondaryInstrumentNameP5.bounded (secondary_instrument_name_p_5 record) /\
      (is_delta_option record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (identifier_prefix_i_4 record) ++
      Date.encode (date record) ++
      InstrumentNameP5.encode (instrument_name_p_5 record) ++
      encode_uint_le 8 (strike record) ++
      encode_bytes 1 (call_put_c_1 record) ++
      SecondaryDate.encode (secondary_date record) ++
      SecondaryInstrumentNameP5.encode (secondary_instrument_name_p_5 record) ++
      encode_uint 1 (is_delta_option record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (identifier_prefix_i_4_value, bytes) =>
          match Date.decode bytes with
          | None => None
          | Some (date_value, bytes) =>
              match InstrumentNameP5.decode bytes with
              | None => None
              | Some (instrument_name_p_5_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (strike_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (call_put_c_1_value, bytes) =>
                          match SecondaryDate.decode bytes with
                          | None => None
                          | Some (secondary_date_value, bytes) =>
                              match SecondaryInstrumentNameP5.decode bytes with
                              | None => None
                              | Some (secondary_instrument_name_p_5_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (is_delta_option_value, bytes) =>
                                      Some ({| identifier_prefix_i_4 := identifier_prefix_i_4_value; date := date_value; instrument_name_p_5 := instrument_name_p_5_value; strike := strike_value; call_put_c_1 := call_put_c_1_value; secondary_date := secondary_date_value; secondary_instrument_name_p_5 := secondary_instrument_name_p_5_value; is_delta_option := is_delta_option_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !Date.encode_length, !InstrumentNameP5.encode_length, !encode_bytes_length, !SecondaryDate.encode_length, !SecondaryInstrumentNameP5.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite Date.decode_encode by exact bound_1.
      rewrite InstrumentNameP5.decode_encode by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite SecondaryDate.decode_encode by exact bound_5.
      rewrite SecondaryInstrumentNameP5.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Date.eq_dec | apply InstrumentNameP5.eq_dec | apply SecondaryDate.eq_dec | apply SecondaryInstrumentNameP5.eq_dec]. Defined.

  End ContractName.

  Module RequestDailyTrendMessage.

    (** Request the on screen trade history for a contract for the current trading session. *)
    Record t := {
      contract_name : ContractName.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      ContractName.bounded (contract_name record).

    Definition encode (record : t) : list byte :=
      ContractName.encode (contract_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match ContractName.decode bytes with
      | None => None
      | Some (contract_name_value, bytes) =>
          Some ({| contract_name := contract_name_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !ContractName.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite ContractName.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply ContractName.eq_dec]. Defined.

  End RequestDailyTrendMessage.

  Module OptionContractSubscriptionMessage.

    (** Subscribe to Display Updates on the contracts listed. *)
    Record t := {
      contract_name : ContractName.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      ContractName.bounded (contract_name record).

    Definition encode (record : t) : list byte :=
      ContractName.encode (contract_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match ContractName.decode bytes with
      | None => None
      | Some (contract_name_value, bytes) =>
          Some ({| contract_name := contract_name_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !ContractName.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite ContractName.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply ContractName.eq_dec]. Defined.

  End OptionContractSubscriptionMessage.

  Module SubscribingToIndicesServiceMessage.

    (** Subscribe or unsubscribe from the indices service. *)
    Record t := {
      subscribe : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (subscribe record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (subscribe record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (subscribe_value, bytes) =>
          Some ({| subscribe := subscribe_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End SubscribingToIndicesServiceMessage.

  Module OptionStatisticsRequestMessage.

    (** Request a Display Update with information for all option contracts traded since the beginning of the trading session. *)
    Record t := {
      contract_name : ContractName.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      ContractName.bounded (contract_name record).

    Definition encode (record : t) : list byte :=
      ContractName.encode (contract_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match ContractName.decode bytes with
      | None => None
      | Some (contract_name_value, bytes) =>
          Some ({| contract_name := contract_name_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !ContractName.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite ContractName.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply ContractName.eq_dec]. Defined.

  End OptionStatisticsRequestMessage.

End NairobiBondsMarketDataV214Client.
