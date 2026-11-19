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
      - a run counted by a field
      - a Reassemble rule
      - a length prefix framing what follows
      - a run filling a byte budget a field states
      - the dispatch that chooses a message by its type

    License: MIT No Attribution
  *)

Module NairobiBondsMarketDataV214Server.

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

  Module ServerMessageHeader.

    (** Table 2: Message Header *)
    Record t := {
      sequence_number : N;
      user_name : UserName.t;
      user_number : N;
      time : Time.t;
      server_message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      UserName.bounded (user_name record) /\
      (user_number record < 256 ^ N.of_nat 4)%N /\
      Time.bounded (time record) /\
      (server_message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (sequence_number record) ++
      UserName.encode (user_name record) ++
      encode_uint_le 4 (user_number record) ++
      Time.encode (time record) ++
      encode_uint 1 (server_message_type record).

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
                      | Some (server_message_type_value, bytes) =>
                          Some ({| sequence_number := sequence_number_value; user_name := user_name_value; user_number := user_number_value; time := time_value; server_message_type := server_message_type_value |}, bytes)
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

  End ServerMessageHeader.

  Module TodayDate.

    (** Today date *)
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

  End TodayDate.

  Module CountryCode.

    (** Indicates the exchanges country code. *)
    Record t := {
      country_code_length_byte : N;
      country_code_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (country_code_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (country_code_characters record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (country_code_length_byte record) ++
      encode_bytes 3 (country_code_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (country_code_length_byte_value, bytes) =>
          match decode_bytes 3 bytes with
          | None => None
          | Some (country_code_characters_value, bytes) =>
              Some ({| country_code_length_byte := country_code_length_byte_value; country_code_characters := country_code_characters_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CountryCode.

  Module PreviousBusinessDay.

    (** Previous Business Day *)
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

  End PreviousBusinessDay.

  Module TextP50.

    (** Indicates further detail on logon failures and success. *)
    Record t := {
      text_p_50_length_byte : N;
      text_p_50_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (text_p_50_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (text_p_50_characters record) = 49.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (text_p_50_length_byte record) ++
      encode_bytes 49 (text_p_50_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (text_p_50_length_byte_value, bytes) =>
          match decode_bytes 49 bytes with
          | None => None
          | Some (text_p_50_characters_value, bytes) =>
              Some ({| text_p_50_length_byte := text_p_50_length_byte_value; text_p_50_characters := text_p_50_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End TextP50.

  Module MemberCodeP6.

    (** Member code of affiliated member. *)
    Record t := {
      member_code_p_6_length_byte : N;
      member_code_p_6_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (member_code_p_6_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (member_code_p_6_characters record) = 5.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (member_code_p_6_length_byte record) ++
      encode_bytes 5 (member_code_p_6_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (member_code_p_6_length_byte_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (member_code_p_6_characters_value, bytes) =>
              Some ({| member_code_p_6_length_byte := member_code_p_6_length_byte_value; member_code_p_6_characters := member_code_p_6_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End MemberCodeP6.

  Module SessionKeyChallengeMessage.

    (** Returned to a user when a successful TCP socket connection is established to the system. *)
    Record t := {
      challenge : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (challenge record) = 243.

    Definition encode (record : t) : list byte :=
      encode_bytes 243 (challenge record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 243 bytes with
      | None => None
      | Some (challenge_value, bytes) =>
          Some ({| challenge := challenge_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 243.
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

  End SessionKeyChallengeMessage.

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

  Module MarketDisplayData.

    (** Market Display Data *)
    Record t := {
      display_sequence : N;
      contract : Contract.t;
      open_price : N;
      instrument_sequence : N;
      date_sequence : N;
      strike_sequence : N;
      second_instrument_sequence : N;
      second_date_sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (display_sequence record < 256 ^ N.of_nat 4)%N /\
      Contract.bounded (contract record) /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (instrument_sequence record < 256 ^ N.of_nat 4)%N /\
      (date_sequence record < 256 ^ N.of_nat 4)%N /\
      (strike_sequence record < 256 ^ N.of_nat 4)%N /\
      (second_instrument_sequence record < 256 ^ N.of_nat 4)%N /\
      (second_date_sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (display_sequence record) ++
      Contract.encode (contract record) ++
      encode_uint_le 8 (open_price record) ++
      encode_uint_le 4 (instrument_sequence record) ++
      encode_uint_le 4 (date_sequence record) ++
      encode_uint_le 4 (strike_sequence record) ++
      encode_uint_le 4 (second_instrument_sequence record) ++
      encode_uint_le 4 (second_date_sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (display_sequence_value, bytes) =>
          match Contract.decode bytes with
          | None => None
          | Some (contract_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (open_price_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (instrument_sequence_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (date_sequence_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (strike_sequence_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (second_instrument_sequence_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (second_date_sequence_value, bytes) =>
                                      Some ({| display_sequence := display_sequence_value; contract := contract_value; open_price := open_price_value; instrument_sequence := instrument_sequence_value; date_sequence := date_sequence_value; strike_sequence := strike_sequence_value; second_instrument_sequence := second_instrument_sequence_value; second_date_sequence := second_date_sequence_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !Contract.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite Contract.decode_encode by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Contract.eq_dec]. Defined.

  End MarketDisplayData.

  Module IsinCode.

    (** ISIN number of the instrument. *)
    Record t := {
      isin_code_length_byte : N;
      isin_code_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (isin_code_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (isin_code_characters record) = 12.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (isin_code_length_byte record) ++
      encode_bytes 12 (isin_code_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (isin_code_length_byte_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_characters_value, bytes) =>
              Some ({| isin_code_length_byte := isin_code_length_byte_value; isin_code_characters := isin_code_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End IsinCode.

  Module DescriptionP62.

    (** A Description of the instrument. *)
    Record t := {
      description_p_62_length_byte : N;
      description_p_62_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (description_p_62_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (description_p_62_characters record) = 61.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (description_p_62_length_byte record) ++
      encode_bytes 61 (description_p_62_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (description_p_62_length_byte_value, bytes) =>
          match decode_bytes 61 bytes with
          | None => None
          | Some (description_p_62_characters_value, bytes) =>
              Some ({| description_p_62_length_byte := description_p_62_length_byte_value; description_p_62_characters := description_p_62_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
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

  End DescriptionP62.

  Module MaturityDate.

    (** Maturity Date *)
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

  End MaturityDate.

  Module IssueDate.

    (** Issue Date *)
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

  End IssueDate.

  Module GroupDescription.

    (** Indicates the group make up for this instrument. *)
    Record t := {
      group_description_length_byte : N;
      group_description_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (group_description_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (group_description_characters record) = 59.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (group_description_length_byte record) ++
      encode_bytes 59 (group_description_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (group_description_length_byte_value, bytes) =>
          match decode_bytes 59 bytes with
          | None => None
          | Some (group_description_characters_value, bytes) =>
              Some ({| group_description_length_byte := group_description_length_byte_value; group_description_characters := group_description_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
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

  End GroupDescription.

  Module FirstTradeReference.

    (** Indicates the reference number of the first trade on this instrument. *)
    Record t := {
      first_trade_reference_length_byte : N;
      first_trade_reference_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (first_trade_reference_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (first_trade_reference_characters record) = 9.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (first_trade_reference_length_byte record) ++
      encode_bytes 9 (first_trade_reference_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (first_trade_reference_length_byte_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (first_trade_reference_characters_value, bytes) =>
              Some ({| first_trade_reference_length_byte := first_trade_reference_length_byte_value; first_trade_reference_characters := first_trade_reference_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End FirstTradeReference.

  Module DisplayName.

    (** This field allows the exchange to indicate how an instrument should be presented. *)
    Record t := {
      display_name_length_byte : N;
      display_name_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (display_name_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (display_name_characters record) = 29.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (display_name_length_byte record) ++
      encode_bytes 29 (display_name_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (display_name_length_byte_value, bytes) =>
          match decode_bytes 29 bytes with
          | None => None
          | Some (display_name_characters_value, bytes) =>
              Some ({| display_name_length_byte := display_name_length_byte_value; display_name_characters := display_name_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End DisplayName.

  Module Classification.

    (** This field defines the instrument classification to which the bonds belongs to. *)
    Record t := {
      classification_length_byte : N;
      classification_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (classification_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (classification_characters record) = 29.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (classification_length_byte record) ++
      encode_bytes 29 (classification_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (classification_length_byte_value, bytes) =>
          match decode_bytes 29 bytes with
          | None => None
          | Some (classification_characters_value, bytes) =>
              Some ({| classification_length_byte := classification_length_byte_value; classification_characters := classification_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End Classification.

  Module VettingAgentName.

    (** The name of any vetting agent for this instrument. *)
    Record t := {
      vetting_agent_name_length_byte : N;
      vetting_agent_name_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (vetting_agent_name_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (vetting_agent_name_characters record) = 29.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (vetting_agent_name_length_byte record) ++
      encode_bytes 29 (vetting_agent_name_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (vetting_agent_name_length_byte_value, bytes) =>
          match decode_bytes 29 bytes with
          | None => None
          | Some (vetting_agent_name_characters_value, bytes) =>
              Some ({| vetting_agent_name_length_byte := vetting_agent_name_length_byte_value; vetting_agent_name_characters := vetting_agent_name_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End VettingAgentName.

  Module VettingAgentContact.

    (** Contact information for the vetting agent. *)
    Record t := {
      vetting_agent_contact_length_byte : N;
      vetting_agent_contact_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (vetting_agent_contact_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (vetting_agent_contact_characters record) = 29.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (vetting_agent_contact_length_byte record) ++
      encode_bytes 29 (vetting_agent_contact_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (vetting_agent_contact_length_byte_value, bytes) =>
          match decode_bytes 29 bytes with
          | None => None
          | Some (vetting_agent_contact_characters_value, bytes) =>
              Some ({| vetting_agent_contact_length_byte := vetting_agent_contact_length_byte_value; vetting_agent_contact_characters := vetting_agent_contact_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End VettingAgentContact.

  Module Sector.

    (** Describes a market sector for a security. *)
    Record t := {
      sector_length_byte : N;
      sector_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sector_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (sector_characters record) = 29.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (sector_length_byte record) ++
      encode_bytes 29 (sector_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (sector_length_byte_value, bytes) =>
          match decode_bytes 29 bytes with
          | None => None
          | Some (sector_characters_value, bytes) =>
              Some ({| sector_length_byte := sector_length_byte_value; sector_characters := sector_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End Sector.

  Module SecurityType.

    (** Categorizes securities into their various types. *)
    Record t := {
      security_type_length_byte : N;
      security_type_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_type_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (security_type_characters record) = 29.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (security_type_length_byte record) ++
      encode_bytes 29 (security_type_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (security_type_length_byte_value, bytes) =>
          match decode_bytes 29 bytes with
          | None => None
          | Some (security_type_characters_value, bytes) =>
              Some ({| security_type_length_byte := security_type_length_byte_value; security_type_characters := security_type_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End SecurityType.

  Module InstrumentsData.

    (** Instruments Data *)
    Record t := {
      instrument_sequence : N;
      trading_session_sequence : N;
      unused_4 : list byte;
      instrument_group_sequence : N;
      future_fee_sequence : N;
      option_fee_sequence : N;
      delivery_fee_sequence : N;
      market_number_c_1 : list byte;
      market_shard_number_c_1 : list byte;
      instrument_name_p_5 : InstrumentNameP5.t;
      instrument_type_number_c_1 : list byte;
      isin_code : IsinCode.t;
      description_p_62 : DescriptionP62.t;
      on_screen : N;
      maturity_date : MaturityDate.t;
      second_unused_4 : list byte;
      nominal_divisor : N;
      issue_date : IssueDate.t;
      linked_to_floating_rate : list byte;
      unused_1 : list byte;
      underlying : N;
      options_exercise_is_percentage : N;
      options_exercise_cost : N;
      group_margin : N;
      vat : N;
      settlement_margin : N;
      physical_settlement : N;
      group_description : GroupDescription.t;
      third_unused_4 : list byte;
      reference_inflation_rate : N;
      minimum_initiation_fee : N;
      first_trade_reference : FirstTradeReference.t;
      unused_5 : list byte;
      country_code : CountryCode.t;
      display_name : DisplayName.t;
      number_of_days_in_a_year : N;
      bond_formula_decimal_places : N;
      coupon_rate : N;
      classification : Classification.t;
      settlement_days : N;
      validated_at_csd : N;
      proprietary_trading_allowed : N;
      vetting_agent_name : VettingAgentName.t;
      vetting_agent_contact : VettingAgentContact.t;
      share_holding_percentage_limit : N;
      sector : Sector.t;
      security_type : SecurityType.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_sequence record < 256 ^ N.of_nat 4)%N /\
      (trading_session_sequence record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (unused_4 record) = 4 /\
      (instrument_group_sequence record < 256 ^ N.of_nat 4)%N /\
      (future_fee_sequence record < 256 ^ N.of_nat 4)%N /\
      (option_fee_sequence record < 256 ^ N.of_nat 4)%N /\
      (delivery_fee_sequence record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_number_c_1 record) = 1 /\
      Datatypes.length (market_shard_number_c_1 record) = 1 /\
      InstrumentNameP5.bounded (instrument_name_p_5 record) /\
      Datatypes.length (instrument_type_number_c_1 record) = 1 /\
      IsinCode.bounded (isin_code record) /\
      DescriptionP62.bounded (description_p_62 record) /\
      (on_screen record < 256 ^ N.of_nat 1)%N /\
      MaturityDate.bounded (maturity_date record) /\
      Datatypes.length (second_unused_4 record) = 4 /\
      (nominal_divisor record < 256 ^ N.of_nat 4)%N /\
      IssueDate.bounded (issue_date record) /\
      Datatypes.length (linked_to_floating_rate record) = 1 /\
      Datatypes.length (unused_1 record) = 1 /\
      (underlying record < 256 ^ N.of_nat 4)%N /\
      (options_exercise_is_percentage record < 256 ^ N.of_nat 1)%N /\
      (options_exercise_cost record < 256 ^ N.of_nat 8)%N /\
      (group_margin record < 256 ^ N.of_nat 8)%N /\
      (vat record < 256 ^ N.of_nat 1)%N /\
      (settlement_margin record < 256 ^ N.of_nat 8)%N /\
      (physical_settlement record < 256 ^ N.of_nat 1)%N /\
      GroupDescription.bounded (group_description record) /\
      Datatypes.length (third_unused_4 record) = 4 /\
      (reference_inflation_rate record < 256 ^ N.of_nat 8)%N /\
      (minimum_initiation_fee record < 256 ^ N.of_nat 8)%N /\
      FirstTradeReference.bounded (first_trade_reference record) /\
      Datatypes.length (unused_5 record) = 5 /\
      CountryCode.bounded (country_code record) /\
      DisplayName.bounded (display_name record) /\
      (number_of_days_in_a_year record < 256 ^ N.of_nat 4)%N /\
      (bond_formula_decimal_places record < 256 ^ N.of_nat 4)%N /\
      (coupon_rate record < 256 ^ N.of_nat 8)%N /\
      Classification.bounded (classification record) /\
      (settlement_days record < 256 ^ N.of_nat 4)%N /\
      (validated_at_csd record < 256 ^ N.of_nat 1)%N /\
      (proprietary_trading_allowed record < 256 ^ N.of_nat 1)%N /\
      VettingAgentName.bounded (vetting_agent_name record) /\
      VettingAgentContact.bounded (vetting_agent_contact record) /\
      (share_holding_percentage_limit record < 256 ^ N.of_nat 8)%N /\
      Sector.bounded (sector record) /\
      SecurityType.bounded (security_type record).

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (instrument_sequence record) ++
      encode_uint_le 4 (trading_session_sequence record) ++
      encode_bytes 4 (unused_4 record) ++
      encode_uint_le 4 (instrument_group_sequence record) ++
      encode_uint_le 4 (future_fee_sequence record) ++
      encode_uint_le 4 (option_fee_sequence record) ++
      encode_uint_le 4 (delivery_fee_sequence record) ++
      encode_bytes 1 (market_number_c_1 record) ++
      encode_bytes 1 (market_shard_number_c_1 record) ++
      InstrumentNameP5.encode (instrument_name_p_5 record) ++
      encode_bytes 1 (instrument_type_number_c_1 record) ++
      IsinCode.encode (isin_code record) ++
      DescriptionP62.encode (description_p_62 record) ++
      encode_uint 1 (on_screen record) ++
      MaturityDate.encode (maturity_date record) ++
      encode_bytes 4 (second_unused_4 record) ++
      encode_uint_le 4 (nominal_divisor record) ++
      IssueDate.encode (issue_date record) ++
      encode_bytes 1 (linked_to_floating_rate record) ++
      encode_bytes 1 (unused_1 record) ++
      encode_uint_le 4 (underlying record) ++
      encode_uint 1 (options_exercise_is_percentage record) ++
      encode_uint_le 8 (options_exercise_cost record) ++
      encode_uint_le 8 (group_margin record) ++
      encode_uint 1 (vat record) ++
      encode_uint_le 8 (settlement_margin record) ++
      encode_uint 1 (physical_settlement record) ++
      GroupDescription.encode (group_description record) ++
      encode_bytes 4 (third_unused_4 record) ++
      encode_uint_le 8 (reference_inflation_rate record) ++
      encode_uint_le 8 (minimum_initiation_fee record) ++
      FirstTradeReference.encode (first_trade_reference record) ++
      encode_bytes 5 (unused_5 record) ++
      CountryCode.encode (country_code record) ++
      DisplayName.encode (display_name record) ++
      encode_uint_le 4 (number_of_days_in_a_year record) ++
      encode_uint_le 4 (bond_formula_decimal_places record) ++
      encode_uint_le 8 (coupon_rate record) ++
      Classification.encode (classification record) ++
      encode_uint_le 4 (settlement_days record) ++
      encode_uint 1 (validated_at_csd record) ++
      encode_uint 1 (proprietary_trading_allowed record) ++
      VettingAgentName.encode (vetting_agent_name record) ++
      VettingAgentContact.encode (vetting_agent_contact record) ++
      encode_uint_le 8 (share_holding_percentage_limit record) ++
      Sector.encode (sector record) ++
      SecurityType.encode (security_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (instrument_sequence_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (trading_session_sequence_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (unused_4_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (instrument_group_sequence_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (future_fee_sequence_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (option_fee_sequence_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (delivery_fee_sequence_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (market_number_c_1_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (market_shard_number_c_1_value, bytes) =>
                                          match InstrumentNameP5.decode bytes with
                                          | None => None
                                          | Some (instrument_name_p_5_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (instrument_type_number_c_1_value, bytes) =>
                                                  match IsinCode.decode bytes with
                                                  | None => None
                                                  | Some (isin_code_value, bytes) =>
                                                      match DescriptionP62.decode bytes with
                                                      | None => None
                                                      | Some (description_p_62_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (on_screen_value, bytes) =>
                                                              match MaturityDate.decode bytes with
                                                              | None => None
                                                              | Some (maturity_date_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (second_unused_4_value, bytes) =>
                                                                      match decode_uint_le 4 bytes with
                                                                      | None => None
                                                                      | Some (nominal_divisor_value, bytes) =>
                                                                          match IssueDate.decode bytes with
                                                                          | None => None
                                                                          | Some (issue_date_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (linked_to_floating_rate_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (unused_1_value, bytes) =>
                                                                                      match decode_uint_le 4 bytes with
                                                                                      | None => None
                                                                                      | Some (underlying_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (options_exercise_is_percentage_value, bytes) =>
                                                                                              match decode_uint_le 8 bytes with
                                                                                              | None => None
                                                                                              | Some (options_exercise_cost_value, bytes) =>
                                                                                                  match decode_uint_le 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (group_margin_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (vat_value, bytes) =>
                                                                                                          match decode_uint_le 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (settlement_margin_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (physical_settlement_value, bytes) =>
                                                                                                                  match GroupDescription.decode bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (group_description_value, bytes) =>
                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (third_unused_4_value, bytes) =>
                                                                                                                          match decode_uint_le 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (reference_inflation_rate_value, bytes) =>
                                                                                                                              match decode_uint_le 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (minimum_initiation_fee_value, bytes) =>
                                                                                                                                  match FirstTradeReference.decode bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (first_trade_reference_value, bytes) =>
                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (unused_5_value, bytes) =>
                                                                                                                                          match CountryCode.decode bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (country_code_value, bytes) =>
                                                                                                                                              match DisplayName.decode bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (display_name_value, bytes) =>
                                                                                                                                                  match decode_uint_le 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (number_of_days_in_a_year_value, bytes) =>
                                                                                                                                                      match decode_uint_le 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bond_formula_decimal_places_value, bytes) =>
                                                                                                                                                          match decode_uint_le 8 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (coupon_rate_value, bytes) =>
                                                                                                                                                              match Classification.decode bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (classification_value, bytes) =>
                                                                                                                                                                  match decode_uint_le 4 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (settlement_days_value, bytes) =>
                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (validated_at_csd_value, bytes) =>
                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (proprietary_trading_allowed_value, bytes) =>
                                                                                                                                                                              match VettingAgentName.decode bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (vetting_agent_name_value, bytes) =>
                                                                                                                                                                                  match VettingAgentContact.decode bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (vetting_agent_contact_value, bytes) =>
                                                                                                                                                                                      match decode_uint_le 8 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (share_holding_percentage_limit_value, bytes) =>
                                                                                                                                                                                          match Sector.decode bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (sector_value, bytes) =>
                                                                                                                                                                                              match SecurityType.decode bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (security_type_value, bytes) =>
                                                                                                                                                                                                  Some ({| instrument_sequence := instrument_sequence_value; trading_session_sequence := trading_session_sequence_value; unused_4 := unused_4_value; instrument_group_sequence := instrument_group_sequence_value; future_fee_sequence := future_fee_sequence_value; option_fee_sequence := option_fee_sequence_value; delivery_fee_sequence := delivery_fee_sequence_value; market_number_c_1 := market_number_c_1_value; market_shard_number_c_1 := market_shard_number_c_1_value; instrument_name_p_5 := instrument_name_p_5_value; instrument_type_number_c_1 := instrument_type_number_c_1_value; isin_code := isin_code_value; description_p_62 := description_p_62_value; on_screen := on_screen_value; maturity_date := maturity_date_value; second_unused_4 := second_unused_4_value; nominal_divisor := nominal_divisor_value; issue_date := issue_date_value; linked_to_floating_rate := linked_to_floating_rate_value; unused_1 := unused_1_value; underlying := underlying_value; options_exercise_is_percentage := options_exercise_is_percentage_value; options_exercise_cost := options_exercise_cost_value; group_margin := group_margin_value; vat := vat_value; settlement_margin := settlement_margin_value; physical_settlement := physical_settlement_value; group_description := group_description_value; third_unused_4 := third_unused_4_value; reference_inflation_rate := reference_inflation_rate_value; minimum_initiation_fee := minimum_initiation_fee_value; first_trade_reference := first_trade_reference_value; unused_5 := unused_5_value; country_code := country_code_value; display_name := display_name_value; number_of_days_in_a_year := number_of_days_in_a_year_value; bond_formula_decimal_places := bond_formula_decimal_places_value; coupon_rate := coupon_rate_value; classification := classification_value; settlement_days := settlement_days_value; validated_at_csd := validated_at_csd_value; proprietary_trading_allowed := proprietary_trading_allowed_value; vetting_agent_name := vetting_agent_name_value; vetting_agent_contact := vetting_agent_contact_value; share_holding_percentage_limit := share_holding_percentage_limit_value; sector := sector_value; security_type := security_type_value |}, bytes)
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
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 486.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !InstrumentNameP5.encode_length, !IsinCode.encode_length, !DescriptionP62.encode_length, !encode_uint_length, !MaturityDate.encode_length, !IssueDate.encode_length, !GroupDescription.encode_length, !FirstTradeReference.encode_length, !CountryCode.encode_length, !DisplayName.encode_length, !Classification.encode_length, !VettingAgentName.encode_length, !VettingAgentContact.encode_length, !Sector.encode_length, !SecurityType.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 bound_46]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite InstrumentNameP5.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite IsinCode.decode_encode by exact bound_11.
      rewrite DescriptionP62.decode_encode by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite MaturityDate.decode_encode by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint_le by exact bound_16.
      rewrite IssueDate.decode_encode by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint_le by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint_le by exact bound_22.
      rewrite decode_encode_uint_le by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint_le by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite GroupDescription.decode_encode by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_uint_le by exact bound_29.
      rewrite decode_encode_uint_le by exact bound_30.
      rewrite FirstTradeReference.decode_encode by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite CountryCode.decode_encode by exact bound_33.
      rewrite DisplayName.decode_encode by exact bound_34.
      rewrite decode_encode_uint_le by exact bound_35.
      rewrite decode_encode_uint_le by exact bound_36.
      rewrite decode_encode_uint_le by exact bound_37.
      rewrite Classification.decode_encode by exact bound_38.
      rewrite decode_encode_uint_le by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite VettingAgentName.decode_encode by exact bound_42.
      rewrite VettingAgentContact.decode_encode by exact bound_43.
      rewrite decode_encode_uint_le by exact bound_44.
      rewrite Sector.decode_encode by exact bound_45.
      rewrite SecurityType.decode_encode by exact bound_46.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply InstrumentNameP5.eq_dec | apply IsinCode.eq_dec | apply DescriptionP62.eq_dec | apply MaturityDate.eq_dec | apply IssueDate.eq_dec | apply GroupDescription.eq_dec | apply FirstTradeReference.eq_dec | apply CountryCode.eq_dec | apply DisplayName.eq_dec | apply Classification.eq_dec | apply VettingAgentName.eq_dec | apply VettingAgentContact.eq_dec | apply Sector.eq_dec | apply SecurityType.eq_dec]. Defined.

  End InstrumentsData.

  Module ExpiryDate.

    (** Expiry Date *)
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

  End ExpiryDate.

  Module ValuationDate.

    (** Valuation Date *)
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

  End ValuationDate.

  Module ClearanceDate.

    (** Clearance Date *)
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

  End ClearanceDate.

  Module ContractDates.

    (** Contract Dates *)
    Record t := {
      instrument_sequence : N;
      contract_date_sequence : N;
      trading_session_sequence : N;
      expiry_date : ExpiryDate.t;
      valuation_date : ValuationDate.t;
      nominal : N;
      strike_interval : N;
      strike_interval_off_screen : N;
      spread_margin : N;
      lot_size : N;
      option_lot_size : N;
      big_depth : N;
      price_rate : list byte;
      max_change : N;
      max_days_move : N;
      max_gap : N;
      unused_1 : list byte;
      options_allowed : N;
      deltas_allowed : N;
      spreads_allowed : N;
      initial_margin : N;
      quote_format_decimal_places : N;
      price_format_decimal_places : N;
      option_premium_format_decimal_places : N;
      price_multiplier : N;
      clearance_date : ClearanceDate.t;
      vsr : N;
      rpve : N;
      volatility_rounding_places : N;
      can_trade_options_onscreen : N;
      can_trade_options_report_only : N;
      can_trade_onscreen : N;
      can_trade_report_only : N;
      price_interval : N;
      minimum_valid_bid_volume_on_screen : N;
      minimum_valid_bid_volume_off_screen : N;
      minimum_valid_bid_volume_on_screen_options : N;
      minimum_valid_bid_volume_off_screen_options : N;
      all_or_nothing_allowed : N;
      at_best_orders_allowed : N;
      stop_orders_allowed : N;
      ice_berg_orders_allowed : N;
      hold_over_orders_allowed : N;
      at_close_orders_allowed : N;
      future_anonymous : N;
      option_anonymous : N;
      unused_17 : list byte;
      rfq_allowed : N;
      quantity_tick_size : N;
      unused_8 : list byte;
      minimum_all_or_nothing_quantity : N;
      minimum_iceberg_quantity : N;
      good_till_cancelled_allowed : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_sequence record < 256 ^ N.of_nat 4)%N /\
      (contract_date_sequence record < 256 ^ N.of_nat 4)%N /\
      (trading_session_sequence record < 256 ^ N.of_nat 4)%N /\
      ExpiryDate.bounded (expiry_date record) /\
      ValuationDate.bounded (valuation_date record) /\
      (nominal record < 256 ^ N.of_nat 8)%N /\
      (strike_interval record < 256 ^ N.of_nat 8)%N /\
      (strike_interval_off_screen record < 256 ^ N.of_nat 8)%N /\
      (spread_margin record < 256 ^ N.of_nat 8)%N /\
      (lot_size record < 256 ^ N.of_nat 4)%N /\
      (option_lot_size record < 256 ^ N.of_nat 4)%N /\
      (big_depth record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price_rate record) = 1 /\
      (max_change record < 256 ^ N.of_nat 8)%N /\
      (max_days_move record < 256 ^ N.of_nat 8)%N /\
      (max_gap record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (unused_1 record) = 1 /\
      (options_allowed record < 256 ^ N.of_nat 1)%N /\
      (deltas_allowed record < 256 ^ N.of_nat 1)%N /\
      (spreads_allowed record < 256 ^ N.of_nat 1)%N /\
      (initial_margin record < 256 ^ N.of_nat 8)%N /\
      (quote_format_decimal_places record < 256 ^ N.of_nat 4)%N /\
      (price_format_decimal_places record < 256 ^ N.of_nat 4)%N /\
      (option_premium_format_decimal_places record < 256 ^ N.of_nat 4)%N /\
      (price_multiplier record < 256 ^ N.of_nat 2)%N /\
      ClearanceDate.bounded (clearance_date record) /\
      (vsr record < 256 ^ N.of_nat 8)%N /\
      (rpve record < 256 ^ N.of_nat 8)%N /\
      (volatility_rounding_places record < 256 ^ N.of_nat 4)%N /\
      (can_trade_options_onscreen record < 256 ^ N.of_nat 1)%N /\
      (can_trade_options_report_only record < 256 ^ N.of_nat 1)%N /\
      (can_trade_onscreen record < 256 ^ N.of_nat 1)%N /\
      (can_trade_report_only record < 256 ^ N.of_nat 1)%N /\
      (price_interval record < 256 ^ N.of_nat 8)%N /\
      (minimum_valid_bid_volume_on_screen record < 256 ^ N.of_nat 4)%N /\
      (minimum_valid_bid_volume_off_screen record < 256 ^ N.of_nat 4)%N /\
      (minimum_valid_bid_volume_on_screen_options record < 256 ^ N.of_nat 4)%N /\
      (minimum_valid_bid_volume_off_screen_options record < 256 ^ N.of_nat 4)%N /\
      (all_or_nothing_allowed record < 256 ^ N.of_nat 1)%N /\
      (at_best_orders_allowed record < 256 ^ N.of_nat 1)%N /\
      (stop_orders_allowed record < 256 ^ N.of_nat 1)%N /\
      (ice_berg_orders_allowed record < 256 ^ N.of_nat 1)%N /\
      (hold_over_orders_allowed record < 256 ^ N.of_nat 1)%N /\
      (at_close_orders_allowed record < 256 ^ N.of_nat 1)%N /\
      (future_anonymous record < 256 ^ N.of_nat 1)%N /\
      (option_anonymous record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (unused_17 record) = 17 /\
      (rfq_allowed record < 256 ^ N.of_nat 1)%N /\
      (quantity_tick_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (unused_8 record) = 8 /\
      (minimum_all_or_nothing_quantity record < 256 ^ N.of_nat 8)%N /\
      (minimum_iceberg_quantity record < 256 ^ N.of_nat 8)%N /\
      (good_till_cancelled_allowed record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (instrument_sequence record) ++
      encode_uint_le 4 (contract_date_sequence record) ++
      encode_uint_le 4 (trading_session_sequence record) ++
      ExpiryDate.encode (expiry_date record) ++
      ValuationDate.encode (valuation_date record) ++
      encode_uint_le 8 (nominal record) ++
      encode_uint_le 8 (strike_interval record) ++
      encode_uint_le 8 (strike_interval_off_screen record) ++
      encode_uint_le 8 (spread_margin record) ++
      encode_uint_le 4 (lot_size record) ++
      encode_uint_le 4 (option_lot_size record) ++
      encode_uint 1 (big_depth record) ++
      encode_bytes 1 (price_rate record) ++
      encode_uint_le 8 (max_change record) ++
      encode_uint_le 8 (max_days_move record) ++
      encode_uint_le 8 (max_gap record) ++
      encode_bytes 1 (unused_1 record) ++
      encode_uint 1 (options_allowed record) ++
      encode_uint 1 (deltas_allowed record) ++
      encode_uint 1 (spreads_allowed record) ++
      encode_uint_le 8 (initial_margin record) ++
      encode_uint_le 4 (quote_format_decimal_places record) ++
      encode_uint_le 4 (price_format_decimal_places record) ++
      encode_uint_le 4 (option_premium_format_decimal_places record) ++
      encode_uint_le 2 (price_multiplier record) ++
      ClearanceDate.encode (clearance_date record) ++
      encode_uint_le 8 (vsr record) ++
      encode_uint_le 8 (rpve record) ++
      encode_uint_le 4 (volatility_rounding_places record) ++
      encode_uint 1 (can_trade_options_onscreen record) ++
      encode_uint 1 (can_trade_options_report_only record) ++
      encode_uint 1 (can_trade_onscreen record) ++
      encode_uint 1 (can_trade_report_only record) ++
      encode_uint_le 8 (price_interval record) ++
      encode_uint_le 4 (minimum_valid_bid_volume_on_screen record) ++
      encode_uint_le 4 (minimum_valid_bid_volume_off_screen record) ++
      encode_uint_le 4 (minimum_valid_bid_volume_on_screen_options record) ++
      encode_uint_le 4 (minimum_valid_bid_volume_off_screen_options record) ++
      encode_uint 1 (all_or_nothing_allowed record) ++
      encode_uint 1 (at_best_orders_allowed record) ++
      encode_uint 1 (stop_orders_allowed record) ++
      encode_uint 1 (ice_berg_orders_allowed record) ++
      encode_uint 1 (hold_over_orders_allowed record) ++
      encode_uint 1 (at_close_orders_allowed record) ++
      encode_uint 1 (future_anonymous record) ++
      encode_uint 1 (option_anonymous record) ++
      encode_bytes 17 (unused_17 record) ++
      encode_uint 1 (rfq_allowed record) ++
      encode_uint_le 4 (quantity_tick_size record) ++
      encode_bytes 8 (unused_8 record) ++
      encode_uint_le 8 (minimum_all_or_nothing_quantity record) ++
      encode_uint_le 8 (minimum_iceberg_quantity record) ++
      encode_uint 1 (good_till_cancelled_allowed record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (instrument_sequence_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (contract_date_sequence_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (trading_session_sequence_value, bytes) =>
                  match ExpiryDate.decode bytes with
                  | None => None
                  | Some (expiry_date_value, bytes) =>
                      match ValuationDate.decode bytes with
                      | None => None
                      | Some (valuation_date_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (nominal_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (strike_interval_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (strike_interval_off_screen_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (spread_margin_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (lot_size_value, bytes) =>
                                              match decode_uint_le 4 bytes with
                                              | None => None
                                              | Some (option_lot_size_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (big_depth_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (price_rate_value, bytes) =>
                                                          match decode_uint_le 8 bytes with
                                                          | None => None
                                                          | Some (max_change_value, bytes) =>
                                                              match decode_uint_le 8 bytes with
                                                              | None => None
                                                              | Some (max_days_move_value, bytes) =>
                                                                  match decode_uint_le 8 bytes with
                                                                  | None => None
                                                                  | Some (max_gap_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (unused_1_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (options_allowed_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (deltas_allowed_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (spreads_allowed_value, bytes) =>
                                                                                      match decode_uint_le 8 bytes with
                                                                                      | None => None
                                                                                      | Some (initial_margin_value, bytes) =>
                                                                                          match decode_uint_le 4 bytes with
                                                                                          | None => None
                                                                                          | Some (quote_format_decimal_places_value, bytes) =>
                                                                                              match decode_uint_le 4 bytes with
                                                                                              | None => None
                                                                                              | Some (price_format_decimal_places_value, bytes) =>
                                                                                                  match decode_uint_le 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (option_premium_format_decimal_places_value, bytes) =>
                                                                                                      match decode_uint_le 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (price_multiplier_value, bytes) =>
                                                                                                          match ClearanceDate.decode bytes with
                                                                                                          | None => None
                                                                                                          | Some (clearance_date_value, bytes) =>
                                                                                                              match decode_uint_le 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (vsr_value, bytes) =>
                                                                                                                  match decode_uint_le 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (rpve_value, bytes) =>
                                                                                                                      match decode_uint_le 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (volatility_rounding_places_value, bytes) =>
                                                                                                                          match decode_uint 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (can_trade_options_onscreen_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (can_trade_options_report_only_value, bytes) =>
                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (can_trade_onscreen_value, bytes) =>
                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (can_trade_report_only_value, bytes) =>
                                                                                                                                          match decode_uint_le 8 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (price_interval_value, bytes) =>
                                                                                                                                              match decode_uint_le 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (minimum_valid_bid_volume_on_screen_value, bytes) =>
                                                                                                                                                  match decode_uint_le 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (minimum_valid_bid_volume_off_screen_value, bytes) =>
                                                                                                                                                      match decode_uint_le 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (minimum_valid_bid_volume_on_screen_options_value, bytes) =>
                                                                                                                                                          match decode_uint_le 4 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (minimum_valid_bid_volume_off_screen_options_value, bytes) =>
                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (all_or_nothing_allowed_value, bytes) =>
                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (at_best_orders_allowed_value, bytes) =>
                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (stop_orders_allowed_value, bytes) =>
                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (ice_berg_orders_allowed_value, bytes) =>
                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (hold_over_orders_allowed_value, bytes) =>
                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (at_close_orders_allowed_value, bytes) =>
                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (future_anonymous_value, bytes) =>
                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (option_anonymous_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 17 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (unused_17_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (rfq_allowed_value, bytes) =>
                                                                                                                                                                                                      match decode_uint_le 4 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (quantity_tick_size_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (unused_8_value, bytes) =>
                                                                                                                                                                                                              match decode_uint_le 8 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (minimum_all_or_nothing_quantity_value, bytes) =>
                                                                                                                                                                                                                  match decode_uint_le 8 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (minimum_iceberg_quantity_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (good_till_cancelled_allowed_value, bytes) =>
                                                                                                                                                                                                                          Some ({| instrument_sequence := instrument_sequence_value; contract_date_sequence := contract_date_sequence_value; trading_session_sequence := trading_session_sequence_value; expiry_date := expiry_date_value; valuation_date := valuation_date_value; nominal := nominal_value; strike_interval := strike_interval_value; strike_interval_off_screen := strike_interval_off_screen_value; spread_margin := spread_margin_value; lot_size := lot_size_value; option_lot_size := option_lot_size_value; big_depth := big_depth_value; price_rate := price_rate_value; max_change := max_change_value; max_days_move := max_days_move_value; max_gap := max_gap_value; unused_1 := unused_1_value; options_allowed := options_allowed_value; deltas_allowed := deltas_allowed_value; spreads_allowed := spreads_allowed_value; initial_margin := initial_margin_value; quote_format_decimal_places := quote_format_decimal_places_value; price_format_decimal_places := price_format_decimal_places_value; option_premium_format_decimal_places := option_premium_format_decimal_places_value; price_multiplier := price_multiplier_value; clearance_date := clearance_date_value; vsr := vsr_value; rpve := rpve_value; volatility_rounding_places := volatility_rounding_places_value; can_trade_options_onscreen := can_trade_options_onscreen_value; can_trade_options_report_only := can_trade_options_report_only_value; can_trade_onscreen := can_trade_onscreen_value; can_trade_report_only := can_trade_report_only_value; price_interval := price_interval_value; minimum_valid_bid_volume_on_screen := minimum_valid_bid_volume_on_screen_value; minimum_valid_bid_volume_off_screen := minimum_valid_bid_volume_off_screen_value; minimum_valid_bid_volume_on_screen_options := minimum_valid_bid_volume_on_screen_options_value; minimum_valid_bid_volume_off_screen_options := minimum_valid_bid_volume_off_screen_options_value; all_or_nothing_allowed := all_or_nothing_allowed_value; at_best_orders_allowed := at_best_orders_allowed_value; stop_orders_allowed := stop_orders_allowed_value; ice_berg_orders_allowed := ice_berg_orders_allowed_value; hold_over_orders_allowed := hold_over_orders_allowed_value; at_close_orders_allowed := at_close_orders_allowed_value; future_anonymous := future_anonymous_value; option_anonymous := option_anonymous_value; unused_17 := unused_17_value; rfq_allowed := rfq_allowed_value; quantity_tick_size := quantity_tick_size_value; unused_8 := unused_8_value; minimum_all_or_nothing_quantity := minimum_all_or_nothing_quantity_value; minimum_iceberg_quantity := minimum_iceberg_quantity_value; good_till_cancelled_allowed := good_till_cancelled_allowed_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 243.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !ExpiryDate.encode_length, !ValuationDate.encode_length, !encode_uint_length, !encode_bytes_length, !ClearanceDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 bound_52]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite ExpiryDate.decode_encode by exact bound_3.
      rewrite ValuationDate.decode_encode by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint_le by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint_le by exact bound_20.
      rewrite decode_encode_uint_le by exact bound_21.
      rewrite decode_encode_uint_le by exact bound_22.
      rewrite decode_encode_uint_le by exact bound_23.
      rewrite decode_encode_uint_le by exact bound_24.
      rewrite ClearanceDate.decode_encode by exact bound_25.
      rewrite decode_encode_uint_le by exact bound_26.
      rewrite decode_encode_uint_le by exact bound_27.
      rewrite decode_encode_uint_le by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_uint_le by exact bound_33.
      rewrite decode_encode_uint_le by exact bound_34.
      rewrite decode_encode_uint_le by exact bound_35.
      rewrite decode_encode_uint_le by exact bound_36.
      rewrite decode_encode_uint_le by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_bytes by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_uint_le by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      rewrite decode_encode_uint_le by exact bound_50.
      rewrite decode_encode_uint_le by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExpiryDate.eq_dec | apply ValuationDate.eq_dec | apply ClearanceDate.eq_dec]. Defined.

  End ContractDates.

  Module StrikeExpiryDate.

    (** Strike Expiry Date *)
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

  End StrikeExpiryDate.

  Module StrikeData.

    (** Strike Data *)
    Record t := {
      strike_sequence_number : N;
      contract_date_sequence : N;
      strike : N;
      strike_expiry_date : StrikeExpiryDate.t;
      deltas : N;
      call_or_put : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (strike_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (contract_date_sequence record < 256 ^ N.of_nat 4)%N /\
      (strike record < 256 ^ N.of_nat 8)%N /\
      StrikeExpiryDate.bounded (strike_expiry_date record) /\
      (deltas record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (call_or_put record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (strike_sequence_number record) ++
      encode_uint_le 4 (contract_date_sequence record) ++
      encode_uint_le 8 (strike record) ++
      StrikeExpiryDate.encode (strike_expiry_date record) ++
      encode_uint 1 (deltas record) ++
      encode_bytes 1 (call_or_put record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (strike_sequence_number_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (contract_date_sequence_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (strike_value, bytes) =>
                  match StrikeExpiryDate.decode bytes with
                  | None => None
                  | Some (strike_expiry_date_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (deltas_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (call_or_put_value, bytes) =>
                              Some ({| strike_sequence_number := strike_sequence_number_value; contract_date_sequence := contract_date_sequence_value; strike := strike_value; strike_expiry_date := strike_expiry_date_value; deltas := deltas_value; call_or_put := call_or_put_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !StrikeExpiryDate.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite StrikeExpiryDate.decode_encode by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply StrikeExpiryDate.eq_dec]. Defined.

  End StrikeData.

  Module MemberCodeP5.

    (** Member code for this member. *)
    Record t := {
      member_code_p_5_length_byte : N;
      member_code_p_5_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (member_code_p_5_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (member_code_p_5_characters record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (member_code_p_5_length_byte record) ++
      encode_bytes 4 (member_code_p_5_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (member_code_p_5_length_byte_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (member_code_p_5_characters_value, bytes) =>
              Some ({| member_code_p_5_length_byte := member_code_p_5_length_byte_value; member_code_p_5_characters := member_code_p_5_characters_value |}, bytes)
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

  End MemberCodeP5.

  Module DescriptionP50.

    (** Name or Description of this member. *)
    Record t := {
      description_p_50_length_byte : N;
      description_p_50_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (description_p_50_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (description_p_50_characters record) = 49.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (description_p_50_length_byte record) ++
      encode_bytes 49 (description_p_50_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (description_p_50_length_byte_value, bytes) =>
          match decode_bytes 49 bytes with
          | None => None
          | Some (description_p_50_characters_value, bytes) =>
              Some ({| description_p_50_length_byte := description_p_50_length_byte_value; description_p_50_characters := description_p_50_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End DescriptionP50.

  Module SorAccount.

    (** SOR Account Number for the Member. *)
    Record t := {
      sor_account_length_byte : N;
      sor_account_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sor_account_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (sor_account_characters record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (sor_account_length_byte record) ++
      encode_bytes 16 (sor_account_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (sor_account_length_byte_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (sor_account_characters_value, bytes) =>
              Some ({| sor_account_length_byte := sor_account_length_byte_value; sor_account_characters := sor_account_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End SorAccount.

  Module MemberData.

    (** Member Data *)
    Record t := {
      member_sequence : N;
      master_member_sequence : N;
      clearing_member_sequence : N;
      member_code_p_5 : MemberCodeP5.t;
      description_p_50 : DescriptionP50.t;
      unused_4 : list byte;
      sor_account : SorAccount.t;
      unused_8 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (member_sequence record < 256 ^ N.of_nat 4)%N /\
      (master_member_sequence record < 256 ^ N.of_nat 4)%N /\
      (clearing_member_sequence record < 256 ^ N.of_nat 4)%N /\
      MemberCodeP5.bounded (member_code_p_5 record) /\
      DescriptionP50.bounded (description_p_50 record) /\
      Datatypes.length (unused_4 record) = 4 /\
      SorAccount.bounded (sor_account record) /\
      Datatypes.length (unused_8 record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (member_sequence record) ++
      encode_uint_le 4 (master_member_sequence record) ++
      encode_uint_le 4 (clearing_member_sequence record) ++
      MemberCodeP5.encode (member_code_p_5 record) ++
      DescriptionP50.encode (description_p_50 record) ++
      encode_bytes 4 (unused_4 record) ++
      SorAccount.encode (sor_account record) ++
      encode_bytes 8 (unused_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (member_sequence_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (master_member_sequence_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (clearing_member_sequence_value, bytes) =>
                  match MemberCodeP5.decode bytes with
                  | None => None
                  | Some (member_code_p_5_value, bytes) =>
                      match DescriptionP50.decode bytes with
                      | None => None
                      | Some (description_p_50_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (unused_4_value, bytes) =>
                              match SorAccount.decode bytes with
                              | None => None
                              | Some (sor_account_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (unused_8_value, bytes) =>
                                      Some ({| member_sequence := member_sequence_value; master_member_sequence := master_member_sequence_value; clearing_member_sequence := clearing_member_sequence_value; member_code_p_5 := member_code_p_5_value; description_p_50 := description_p_50_value; unused_4 := unused_4_value; sor_account := sor_account_value; unused_8 := unused_8_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 96.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !MemberCodeP5.encode_length, !DescriptionP50.encode_length, !encode_bytes_length, !SorAccount.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite MemberCodeP5.decode_encode by exact bound_3.
      rewrite DescriptionP50.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite SorAccount.decode_encode by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MemberCodeP5.eq_dec | apply DescriptionP50.eq_dec | apply SorAccount.eq_dec]. Defined.

  End MemberData.

  Module MtmData.

    (** MTM Data *)
    Record t := {
      instrument_sequence : N;
      date_sequence : N;
      strike_sequence : N;
      contract : Contract.t;
      days_closing_price : N;
      days_closing_rate : N;
      open_interest : N;
      date : Date.t;
      spot_price : N;
      volatility : N;
      high_price : N;
      low_price : N;
      days_volume_d_8 : N;
      shares_in_issue : N;
      open_price : N;
      previous_close_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_sequence record < 256 ^ N.of_nat 4)%N /\
      (date_sequence record < 256 ^ N.of_nat 4)%N /\
      (strike_sequence record < 256 ^ N.of_nat 4)%N /\
      Contract.bounded (contract record) /\
      (days_closing_price record < 256 ^ N.of_nat 8)%N /\
      (days_closing_rate record < 256 ^ N.of_nat 8)%N /\
      (open_interest record < 256 ^ N.of_nat 8)%N /\
      Date.bounded (date record) /\
      (spot_price record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (days_volume_d_8 record < 256 ^ N.of_nat 8)%N /\
      (shares_in_issue record < 256 ^ N.of_nat 8)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (previous_close_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (instrument_sequence record) ++
      encode_uint_le 4 (date_sequence record) ++
      encode_uint_le 4 (strike_sequence record) ++
      Contract.encode (contract record) ++
      encode_uint_le 8 (days_closing_price record) ++
      encode_uint_le 8 (days_closing_rate record) ++
      encode_uint_le 8 (open_interest record) ++
      Date.encode (date record) ++
      encode_uint_le 8 (spot_price record) ++
      encode_uint_le 8 (volatility record) ++
      encode_uint_le 8 (high_price record) ++
      encode_uint_le 8 (low_price record) ++
      encode_uint_le 8 (days_volume_d_8 record) ++
      encode_uint_le 8 (shares_in_issue record) ++
      encode_uint_le 8 (open_price record) ++
      encode_uint_le 8 (previous_close_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (instrument_sequence_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (date_sequence_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (strike_sequence_value, bytes) =>
                  match Contract.decode bytes with
                  | None => None
                  | Some (contract_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (days_closing_price_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (days_closing_rate_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (open_interest_value, bytes) =>
                                  match Date.decode bytes with
                                  | None => None
                                  | Some (date_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (spot_price_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (volatility_value, bytes) =>
                                              match decode_uint_le 8 bytes with
                                              | None => None
                                              | Some (high_price_value, bytes) =>
                                                  match decode_uint_le 8 bytes with
                                                  | None => None
                                                  | Some (low_price_value, bytes) =>
                                                      match decode_uint_le 8 bytes with
                                                      | None => None
                                                      | Some (days_volume_d_8_value, bytes) =>
                                                          match decode_uint_le 8 bytes with
                                                          | None => None
                                                          | Some (shares_in_issue_value, bytes) =>
                                                              match decode_uint_le 8 bytes with
                                                              | None => None
                                                              | Some (open_price_value, bytes) =>
                                                                  match decode_uint_le 8 bytes with
                                                                  | None => None
                                                                  | Some (previous_close_price_value, bytes) =>
                                                                      Some ({| instrument_sequence := instrument_sequence_value; date_sequence := date_sequence_value; strike_sequence := strike_sequence_value; contract := contract_value; days_closing_price := days_closing_price_value; days_closing_rate := days_closing_rate_value; open_interest := open_interest_value; date := date_value; spot_price := spot_price_value; volatility := volatility_value; high_price := high_price_value; low_price := low_price_value; days_volume_d_8 := days_volume_d_8_value; shares_in_issue := shares_in_issue_value; open_price := open_price_value; previous_close_price := previous_close_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 160.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !Contract.encode_length, !Date.encode_length. reflexivity.
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
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite Contract.decode_encode by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite Date.decode_encode by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint_le by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Contract.eq_dec | apply Date.eq_dec]. Defined.

  End MtmData.

  Module HolidayDate.

    (** Holiday Date *)
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

  End HolidayDate.

  Module HolidayData.

    (** Holiday Data *)
    Record t := {
      holiday_sequence : N;
      country_code : CountryCode.t;
      holiday_date : HolidayDate.t;
      reminder_only : N;
      is_early_close : N;
      is_futures_close_out : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (holiday_sequence record < 256 ^ N.of_nat 4)%N /\
      CountryCode.bounded (country_code record) /\
      HolidayDate.bounded (holiday_date record) /\
      (reminder_only record < 256 ^ N.of_nat 1)%N /\
      (is_early_close record < 256 ^ N.of_nat 1)%N /\
      (is_futures_close_out record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (holiday_sequence record) ++
      CountryCode.encode (country_code record) ++
      HolidayDate.encode (holiday_date record) ++
      encode_uint 1 (reminder_only record) ++
      encode_uint 1 (is_early_close record) ++
      encode_uint 1 (is_futures_close_out record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (holiday_sequence_value, bytes) =>
          match CountryCode.decode bytes with
          | None => None
          | Some (country_code_value, bytes) =>
              match HolidayDate.decode bytes with
              | None => None
              | Some (holiday_date_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reminder_only_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (is_early_close_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (is_futures_close_out_value, bytes) =>
                              Some ({| holiday_sequence := holiday_sequence_value; country_code := country_code_value; holiday_date := holiday_date_value; reminder_only := reminder_only_value; is_early_close := is_early_close_value; is_futures_close_out := is_futures_close_out_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !CountryCode.encode_length, !HolidayDate.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite CountryCode.decode_encode by exact bound_1.
      rewrite HolidayDate.decode_encode by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply CountryCode.eq_dec | apply HolidayDate.eq_dec]. Defined.

  End HolidayData.

  Module InstrumentTypeCode.

    (** Indicates the instrument type code. *)
    Record t := {
      instrument_type_code_length_byte : N;
      instrument_type_code_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_type_code_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (instrument_type_code_characters record) = 9.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_type_code_length_byte record) ++
      encode_bytes 9 (instrument_type_code_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_type_code_length_byte_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (instrument_type_code_characters_value, bytes) =>
              Some ({| instrument_type_code_length_byte := instrument_type_code_length_byte_value; instrument_type_code_characters := instrument_type_code_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End InstrumentTypeCode.

  Module InstrumentTypeName.

    (** A description of the instrument type. *)
    Record t := {
      instrument_type_name_length_byte : N;
      instrument_type_name_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_type_name_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (instrument_type_name_characters record) = 24.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_type_name_length_byte record) ++
      encode_bytes 24 (instrument_type_name_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_type_name_length_byte_value, bytes) =>
          match decode_bytes 24 bytes with
          | None => None
          | Some (instrument_type_name_characters_value, bytes) =>
              Some ({| instrument_type_name_length_byte := instrument_type_name_length_byte_value; instrument_type_name_characters := instrument_type_name_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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

  End InstrumentTypeName.

  Module InstrumentTypes.

    (** Instrument Types *)
    Record t := {
      instrument_type_sequence : N;
      unused_4 : list byte;
      instrument_type_number_i_4 : N;
      identifier_prefix_c_1 : list byte;
      instrument_type_code : InstrumentTypeCode.t;
      instrument_type_name : InstrumentTypeName.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_type_sequence record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (unused_4 record) = 4 /\
      (instrument_type_number_i_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (identifier_prefix_c_1 record) = 1 /\
      InstrumentTypeCode.bounded (instrument_type_code record) /\
      InstrumentTypeName.bounded (instrument_type_name record).

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (instrument_type_sequence record) ++
      encode_bytes 4 (unused_4 record) ++
      encode_uint_le 4 (instrument_type_number_i_4 record) ++
      encode_bytes 1 (identifier_prefix_c_1 record) ++
      InstrumentTypeCode.encode (instrument_type_code record) ++
      InstrumentTypeName.encode (instrument_type_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (instrument_type_sequence_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (unused_4_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (instrument_type_number_i_4_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (identifier_prefix_c_1_value, bytes) =>
                      match InstrumentTypeCode.decode bytes with
                      | None => None
                      | Some (instrument_type_code_value, bytes) =>
                          match InstrumentTypeName.decode bytes with
                          | None => None
                          | Some (instrument_type_name_value, bytes) =>
                              Some ({| instrument_type_sequence := instrument_type_sequence_value; unused_4 := unused_4_value; instrument_type_number_i_4 := instrument_type_number_i_4_value; identifier_prefix_c_1 := identifier_prefix_c_1_value; instrument_type_code := instrument_type_code_value; instrument_type_name := instrument_type_name_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !InstrumentTypeCode.encode_length, !InstrumentTypeName.encode_length. reflexivity.
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
      rewrite InstrumentTypeCode.decode_encode by exact bound_4.
      rewrite InstrumentTypeName.decode_encode by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply InstrumentTypeCode.eq_dec | apply InstrumentTypeName.eq_dec]. Defined.

  End InstrumentTypes.

  Module ClearingMemberCode.

    (** This is the code used for the clearing member. *)
    Record t := {
      clearing_member_code_length_byte : N;
      clearing_member_code_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (clearing_member_code_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_member_code_characters record) = 5.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (clearing_member_code_length_byte record) ++
      encode_bytes 5 (clearing_member_code_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (clearing_member_code_length_byte_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (clearing_member_code_characters_value, bytes) =>
              Some ({| clearing_member_code_length_byte := clearing_member_code_length_byte_value; clearing_member_code_characters := clearing_member_code_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End ClearingMemberCode.

  Module ClearingMemberDescription.

    (** This is the Description of the clearing member. *)
    Record t := {
      clearing_member_description_length_byte : N;
      clearing_member_description_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (clearing_member_description_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_member_description_characters record) = 49.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (clearing_member_description_length_byte record) ++
      encode_bytes 49 (clearing_member_description_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (clearing_member_description_length_byte_value, bytes) =>
          match decode_bytes 49 bytes with
          | None => None
          | Some (clearing_member_description_characters_value, bytes) =>
              Some ({| clearing_member_description_length_byte := clearing_member_description_length_byte_value; clearing_member_description_characters := clearing_member_description_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End ClearingMemberDescription.

  Module ClearingMemberData.

    (** Clearing Member Data *)
    Record t := {
      clearing_member_sequence : N;
      clearing_member_code : ClearingMemberCode.t;
      clearing_member_description : ClearingMemberDescription.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (clearing_member_sequence record < 256 ^ N.of_nat 4)%N /\
      ClearingMemberCode.bounded (clearing_member_code record) /\
      ClearingMemberDescription.bounded (clearing_member_description record).

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (clearing_member_sequence record) ++
      ClearingMemberCode.encode (clearing_member_code record) ++
      ClearingMemberDescription.encode (clearing_member_description record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (clearing_member_sequence_value, bytes) =>
          match ClearingMemberCode.decode bytes with
          | None => None
          | Some (clearing_member_code_value, bytes) =>
              match ClearingMemberDescription.decode bytes with
              | None => None
              | Some (clearing_member_description_value, bytes) =>
                  Some ({| clearing_member_sequence := clearing_member_sequence_value; clearing_member_code := clearing_member_code_value; clearing_member_description := clearing_member_description_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !ClearingMemberCode.encode_length, !ClearingMemberDescription.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite ClearingMemberCode.decode_encode by exact bound_1.
      rewrite ClearingMemberDescription.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply ClearingMemberCode.eq_dec | apply ClearingMemberDescription.eq_dec]. Defined.

  End ClearingMemberData.

  Module AnnouncementDate.

    (** Announcement Date *)
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

  End AnnouncementDate.

  Module AnnouncementTime.

    (** Announcement Time *)
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

  End AnnouncementTime.

  Module Announcement.

    (** Announcement as sent by the exchange. *)
    Record t := {
      announcement_length_byte : N;
      announcement_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (announcement_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (announcement_characters record) = 254.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (announcement_length_byte record) ++
      encode_bytes 254 (announcement_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (announcement_length_byte_value, bytes) =>
          match decode_bytes 254 bytes with
          | None => None
          | Some (announcement_characters_value, bytes) =>
              Some ({| announcement_length_byte := announcement_length_byte_value; announcement_characters := announcement_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 255.
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

  End Announcement.

  Module ExchangeAnnouncements.

    (** Exchange Announcements *)
    Record t := {
      id_market : N;
      announcement_sequence : N;
      announcement_date : AnnouncementDate.t;
      announcement_time : AnnouncementTime.t;
      announcement : Announcement.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (id_market record < 256 ^ N.of_nat 4)%N /\
      (announcement_sequence record < 256 ^ N.of_nat 4)%N /\
      AnnouncementDate.bounded (announcement_date record) /\
      AnnouncementTime.bounded (announcement_time record) /\
      Announcement.bounded (announcement record).

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (id_market record) ++
      encode_uint_le 4 (announcement_sequence record) ++
      AnnouncementDate.encode (announcement_date record) ++
      AnnouncementTime.encode (announcement_time record) ++
      Announcement.encode (announcement record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (id_market_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (announcement_sequence_value, bytes) =>
              match AnnouncementDate.decode bytes with
              | None => None
              | Some (announcement_date_value, bytes) =>
                  match AnnouncementTime.decode bytes with
                  | None => None
                  | Some (announcement_time_value, bytes) =>
                      match Announcement.decode bytes with
                      | None => None
                      | Some (announcement_value, bytes) =>
                          Some ({| id_market := id_market_value; announcement_sequence := announcement_sequence_value; announcement_date := announcement_date_value; announcement_time := announcement_time_value; announcement := announcement_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 279.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !AnnouncementDate.encode_length, !AnnouncementTime.encode_length, !Announcement.encode_length. reflexivity.
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
      rewrite AnnouncementDate.decode_encode by exact bound_2.
      rewrite AnnouncementTime.decode_encode by exact bound_3.
      rewrite Announcement.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply AnnouncementDate.eq_dec | apply AnnouncementTime.eq_dec | apply Announcement.eq_dec]. Defined.

  End ExchangeAnnouncements.

  Module MessageCategoryValue.

    (** Indicates the value which is associated with the category type. *)
    Record t := {
      message_category_value_length_byte : N;
      message_category_value_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_category_value_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (message_category_value_characters record) = 49.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_category_value_length_byte record) ++
      encode_bytes 49 (message_category_value_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_category_value_length_byte_value, bytes) =>
          match decode_bytes 49 bytes with
          | None => None
          | Some (message_category_value_characters_value, bytes) =>
              Some ({| message_category_value_length_byte := message_category_value_length_byte_value; message_category_value_characters := message_category_value_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End MessageCategoryValue.

  Module MessageP255.

    (** Indicates the text for this segment of the news message. *)
    Record t := {
      message_p_255_length_byte : N;
      message_p_255_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_p_255_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (message_p_255_characters record) = 254.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_p_255_length_byte record) ++
      encode_bytes 254 (message_p_255_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_p_255_length_byte_value, bytes) =>
          match decode_bytes 254 bytes with
          | None => None
          | Some (message_p_255_characters_value, bytes) =>
              Some ({| message_p_255_length_byte := message_p_255_length_byte_value; message_p_255_characters := message_p_255_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 255.
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

  End MessageP255.

  Module NewsService.

    (** News Service *)
    Record t := {
      date : Date.t;
      time : Time.t;
      message_category_type : N;
      message_category_value : MessageCategoryValue.t;
      news_number : N;
      total_number_of_segments : N;
      segment_number : N;
      message_p_255 : MessageP255.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Date.bounded (date record) /\
      Time.bounded (time record) /\
      (message_category_type record < 256 ^ N.of_nat 2)%N /\
      MessageCategoryValue.bounded (message_category_value record) /\
      (news_number record < 256 ^ N.of_nat 2)%N /\
      (total_number_of_segments record < 256 ^ N.of_nat 2)%N /\
      (segment_number record < 256 ^ N.of_nat 2)%N /\
      MessageP255.bounded (message_p_255 record).

    Definition encode (record : t) : list byte :=
      Date.encode (date record) ++
      Time.encode (time record) ++
      encode_uint_le 2 (message_category_type record) ++
      MessageCategoryValue.encode (message_category_value record) ++
      encode_uint_le 2 (news_number record) ++
      encode_uint_le 2 (total_number_of_segments record) ++
      encode_uint_le 2 (segment_number record) ++
      MessageP255.encode (message_p_255 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Date.decode bytes with
      | None => None
      | Some (date_value, bytes) =>
          match Time.decode bytes with
          | None => None
          | Some (time_value, bytes) =>
              match decode_uint_le 2 bytes with
              | None => None
              | Some (message_category_type_value, bytes) =>
                  match MessageCategoryValue.decode bytes with
                  | None => None
                  | Some (message_category_value_value, bytes) =>
                      match decode_uint_le 2 bytes with
                      | None => None
                      | Some (news_number_value, bytes) =>
                          match decode_uint_le 2 bytes with
                          | None => None
                          | Some (total_number_of_segments_value, bytes) =>
                              match decode_uint_le 2 bytes with
                              | None => None
                              | Some (segment_number_value, bytes) =>
                                  match MessageP255.decode bytes with
                                  | None => None
                                  | Some (message_p_255_value, bytes) =>
                                      Some ({| date := date_value; time := time_value; message_category_type := message_category_type_value; message_category_value := message_category_value_value; news_number := news_number_value; total_number_of_segments := total_number_of_segments_value; segment_number := segment_number_value; message_p_255 := message_p_255_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 329.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Date.encode_length, !Time.encode_length, !encode_uint_le_length, !MessageCategoryValue.encode_length, !MessageP255.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Date.decode_encode by exact bound_0.
      rewrite Time.decode_encode by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite MessageCategoryValue.decode_encode by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite MessageP255.decode_encode by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Date.eq_dec | apply Time.eq_dec | apply MessageCategoryValue.eq_dec | apply MessageP255.eq_dec]. Defined.

  End NewsService.

  Module CouponDate.

    (** Coupon Date *)
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

  End CouponDate.

  Module BooksCloseDate.

    (** Books Close Date *)
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

  End BooksCloseDate.

  Module CouponInformation.

    (** Coupon Information *)
    Record t := {
      coupon_sequence : N;
      instrument_sequence : N;
      coupon_date : CouponDate.t;
      books_close_date : BooksCloseDate.t;
      coupon_rate : N;
      redemption_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (coupon_sequence record < 256 ^ N.of_nat 4)%N /\
      (instrument_sequence record < 256 ^ N.of_nat 4)%N /\
      CouponDate.bounded (coupon_date record) /\
      BooksCloseDate.bounded (books_close_date record) /\
      (coupon_rate record < 256 ^ N.of_nat 8)%N /\
      (redemption_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (coupon_sequence record) ++
      encode_uint_le 4 (instrument_sequence record) ++
      CouponDate.encode (coupon_date record) ++
      BooksCloseDate.encode (books_close_date record) ++
      encode_uint_le 8 (coupon_rate record) ++
      encode_uint_le 8 (redemption_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (coupon_sequence_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_sequence_value, bytes) =>
              match CouponDate.decode bytes with
              | None => None
              | Some (coupon_date_value, bytes) =>
                  match BooksCloseDate.decode bytes with
                  | None => None
                  | Some (books_close_date_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (coupon_rate_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (redemption_value_value, bytes) =>
                              Some ({| coupon_sequence := coupon_sequence_value; instrument_sequence := instrument_sequence_value; coupon_date := coupon_date_value; books_close_date := books_close_date_value; coupon_rate := coupon_rate_value; redemption_value := redemption_value_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !CouponDate.encode_length, !BooksCloseDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite CouponDate.decode_encode by exact bound_2.
      rewrite BooksCloseDate.decode_encode by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply CouponDate.eq_dec | apply BooksCloseDate.eq_dec]. Defined.

  End CouponInformation.

  Module TradingSessionName.

    (** Indicates the name of the trading session. *)
    Record t := {
      trading_session_name_length_byte : N;
      trading_session_name_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trading_session_name_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trading_session_name_characters record) = 55.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (trading_session_name_length_byte record) ++
      encode_bytes 55 (trading_session_name_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (trading_session_name_length_byte_value, bytes) =>
          match decode_bytes 55 bytes with
          | None => None
          | Some (trading_session_name_characters_value, bytes) =>
              Some ({| trading_session_name_length_byte := trading_session_name_length_byte_value; trading_session_name_characters := trading_session_name_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
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

  End TradingSessionName.

  Module OpeningAuctionStartTime.

    (** Opening Auction Start Time *)
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

  End OpeningAuctionStartTime.

  Module OpeningAuctionCloseTime.

    (** Opening Auction Close Time *)
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

  End OpeningAuctionCloseTime.

  Module ClosingAuctionStartTime.

    (** Closing Auction Start Time *)
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

  End ClosingAuctionStartTime.

  Module ClosingAuctionCloseTime.

    (** Closing Auction Close Time *)
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

  End ClosingAuctionCloseTime.

  Module ContractOpenTime.

    (** Contract Open Time *)
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

  End ContractOpenTime.

  Module ContractCloseTime.

    (** Contract Close Time *)
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

  End ContractCloseTime.

  Module IntradayAuctionOneStartTime.

    (** Intraday Auction One Start Time *)
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

  End IntradayAuctionOneStartTime.

  Module IntradayAuctionOneAuctionCloseTime.

    (** Intraday Auction One Auction Close Time *)
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

  End IntradayAuctionOneAuctionCloseTime.

  Module IntradayAuctionTwoStartTime.

    (** Intraday Auction Two Start Time *)
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

  End IntradayAuctionTwoStartTime.

  Module IntradayAuctionTwoAuctionCloseTime.

    (** Intraday Auction Two Auction Close Time *)
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

  End IntradayAuctionTwoAuctionCloseTime.

  Module IntradayAuctionThreeStartTime.

    (** Intraday Auction Three Start Time *)
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

  End IntradayAuctionThreeStartTime.

  Module IntradayAuctionThreeAuctionCloseTime.

    (** Intraday Auction Three Auction Close Time *)
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

  End IntradayAuctionThreeAuctionCloseTime.

  Module OvernightAdminOpenTime.

    (** Overnight Admin Open Time *)
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

  End OvernightAdminOpenTime.

  Module OvernightAdminCloseTime.

    (** Overnight Admin Close Time *)
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

  End OvernightAdminCloseTime.

  Module AdminPeriodCloseTime.

    (** Admin Period Close Time *)
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

  End AdminPeriodCloseTime.

  Module PreOpenOrderEntryOpenTime.

    (** Pre-open order entry Open Time *)
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

  End PreOpenOrderEntryOpenTime.

  Module PreOpenOrderEntryCloseTime.

    (** Pre-open order entry Close Time *)
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

  End PreOpenOrderEntryCloseTime.

  Module TradingSessions.

    (** Trading Sessions *)
    Record t := {
      trading_session_sequence : N;
      trading_session_name : TradingSessionName.t;
      opening_auction_start_time : OpeningAuctionStartTime.t;
      opening_auction_close_time : OpeningAuctionCloseTime.t;
      closing_auction_start_time : ClosingAuctionStartTime.t;
      closing_auction_close_time : ClosingAuctionCloseTime.t;
      contract_open_time : ContractOpenTime.t;
      contract_close_time : ContractCloseTime.t;
      intraday_auction_one_start_time : IntradayAuctionOneStartTime.t;
      intraday_auction_one_auction_close_time : IntradayAuctionOneAuctionCloseTime.t;
      intraday_auction_two_start_time : IntradayAuctionTwoStartTime.t;
      intraday_auction_two_auction_close_time : IntradayAuctionTwoAuctionCloseTime.t;
      intraday_auction_three_start_time : IntradayAuctionThreeStartTime.t;
      intraday_auction_three_auction_close_time : IntradayAuctionThreeAuctionCloseTime.t;
      overnight_admin_open_time : OvernightAdminOpenTime.t;
      overnight_admin_close_time : OvernightAdminCloseTime.t;
      admin_period_close_time : AdminPeriodCloseTime.t;
      unused_8 : list byte;
      pre_open_order_entry_open_time : PreOpenOrderEntryOpenTime.t;
      pre_open_order_entry_close_time : PreOpenOrderEntryCloseTime.t;
      second_unused_8 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trading_session_sequence record < 256 ^ N.of_nat 4)%N /\
      TradingSessionName.bounded (trading_session_name record) /\
      OpeningAuctionStartTime.bounded (opening_auction_start_time record) /\
      OpeningAuctionCloseTime.bounded (opening_auction_close_time record) /\
      ClosingAuctionStartTime.bounded (closing_auction_start_time record) /\
      ClosingAuctionCloseTime.bounded (closing_auction_close_time record) /\
      ContractOpenTime.bounded (contract_open_time record) /\
      ContractCloseTime.bounded (contract_close_time record) /\
      IntradayAuctionOneStartTime.bounded (intraday_auction_one_start_time record) /\
      IntradayAuctionOneAuctionCloseTime.bounded (intraday_auction_one_auction_close_time record) /\
      IntradayAuctionTwoStartTime.bounded (intraday_auction_two_start_time record) /\
      IntradayAuctionTwoAuctionCloseTime.bounded (intraday_auction_two_auction_close_time record) /\
      IntradayAuctionThreeStartTime.bounded (intraday_auction_three_start_time record) /\
      IntradayAuctionThreeAuctionCloseTime.bounded (intraday_auction_three_auction_close_time record) /\
      OvernightAdminOpenTime.bounded (overnight_admin_open_time record) /\
      OvernightAdminCloseTime.bounded (overnight_admin_close_time record) /\
      AdminPeriodCloseTime.bounded (admin_period_close_time record) /\
      Datatypes.length (unused_8 record) = 8 /\
      PreOpenOrderEntryOpenTime.bounded (pre_open_order_entry_open_time record) /\
      PreOpenOrderEntryCloseTime.bounded (pre_open_order_entry_close_time record) /\
      Datatypes.length (second_unused_8 record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (trading_session_sequence record) ++
      TradingSessionName.encode (trading_session_name record) ++
      OpeningAuctionStartTime.encode (opening_auction_start_time record) ++
      OpeningAuctionCloseTime.encode (opening_auction_close_time record) ++
      ClosingAuctionStartTime.encode (closing_auction_start_time record) ++
      ClosingAuctionCloseTime.encode (closing_auction_close_time record) ++
      ContractOpenTime.encode (contract_open_time record) ++
      ContractCloseTime.encode (contract_close_time record) ++
      IntradayAuctionOneStartTime.encode (intraday_auction_one_start_time record) ++
      IntradayAuctionOneAuctionCloseTime.encode (intraday_auction_one_auction_close_time record) ++
      IntradayAuctionTwoStartTime.encode (intraday_auction_two_start_time record) ++
      IntradayAuctionTwoAuctionCloseTime.encode (intraday_auction_two_auction_close_time record) ++
      IntradayAuctionThreeStartTime.encode (intraday_auction_three_start_time record) ++
      IntradayAuctionThreeAuctionCloseTime.encode (intraday_auction_three_auction_close_time record) ++
      OvernightAdminOpenTime.encode (overnight_admin_open_time record) ++
      OvernightAdminCloseTime.encode (overnight_admin_close_time record) ++
      AdminPeriodCloseTime.encode (admin_period_close_time record) ++
      encode_bytes 8 (unused_8 record) ++
      PreOpenOrderEntryOpenTime.encode (pre_open_order_entry_open_time record) ++
      PreOpenOrderEntryCloseTime.encode (pre_open_order_entry_close_time record) ++
      encode_bytes 8 (second_unused_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (trading_session_sequence_value, bytes) =>
          match TradingSessionName.decode bytes with
          | None => None
          | Some (trading_session_name_value, bytes) =>
              match OpeningAuctionStartTime.decode bytes with
              | None => None
              | Some (opening_auction_start_time_value, bytes) =>
                  match OpeningAuctionCloseTime.decode bytes with
                  | None => None
                  | Some (opening_auction_close_time_value, bytes) =>
                      match ClosingAuctionStartTime.decode bytes with
                      | None => None
                      | Some (closing_auction_start_time_value, bytes) =>
                          match ClosingAuctionCloseTime.decode bytes with
                          | None => None
                          | Some (closing_auction_close_time_value, bytes) =>
                              match ContractOpenTime.decode bytes with
                              | None => None
                              | Some (contract_open_time_value, bytes) =>
                                  match ContractCloseTime.decode bytes with
                                  | None => None
                                  | Some (contract_close_time_value, bytes) =>
                                      match IntradayAuctionOneStartTime.decode bytes with
                                      | None => None
                                      | Some (intraday_auction_one_start_time_value, bytes) =>
                                          match IntradayAuctionOneAuctionCloseTime.decode bytes with
                                          | None => None
                                          | Some (intraday_auction_one_auction_close_time_value, bytes) =>
                                              match IntradayAuctionTwoStartTime.decode bytes with
                                              | None => None
                                              | Some (intraday_auction_two_start_time_value, bytes) =>
                                                  match IntradayAuctionTwoAuctionCloseTime.decode bytes with
                                                  | None => None
                                                  | Some (intraday_auction_two_auction_close_time_value, bytes) =>
                                                      match IntradayAuctionThreeStartTime.decode bytes with
                                                      | None => None
                                                      | Some (intraday_auction_three_start_time_value, bytes) =>
                                                          match IntradayAuctionThreeAuctionCloseTime.decode bytes with
                                                          | None => None
                                                          | Some (intraday_auction_three_auction_close_time_value, bytes) =>
                                                              match OvernightAdminOpenTime.decode bytes with
                                                              | None => None
                                                              | Some (overnight_admin_open_time_value, bytes) =>
                                                                  match OvernightAdminCloseTime.decode bytes with
                                                                  | None => None
                                                                  | Some (overnight_admin_close_time_value, bytes) =>
                                                                      match AdminPeriodCloseTime.decode bytes with
                                                                      | None => None
                                                                      | Some (admin_period_close_time_value, bytes) =>
                                                                          match decode_bytes 8 bytes with
                                                                          | None => None
                                                                          | Some (unused_8_value, bytes) =>
                                                                              match PreOpenOrderEntryOpenTime.decode bytes with
                                                                              | None => None
                                                                              | Some (pre_open_order_entry_open_time_value, bytes) =>
                                                                                  match PreOpenOrderEntryCloseTime.decode bytes with
                                                                                  | None => None
                                                                                  | Some (pre_open_order_entry_close_time_value, bytes) =>
                                                                                      match decode_bytes 8 bytes with
                                                                                      | None => None
                                                                                      | Some (second_unused_8_value, bytes) =>
                                                                                          Some ({| trading_session_sequence := trading_session_sequence_value; trading_session_name := trading_session_name_value; opening_auction_start_time := opening_auction_start_time_value; opening_auction_close_time := opening_auction_close_time_value; closing_auction_start_time := closing_auction_start_time_value; closing_auction_close_time := closing_auction_close_time_value; contract_open_time := contract_open_time_value; contract_close_time := contract_close_time_value; intraday_auction_one_start_time := intraday_auction_one_start_time_value; intraday_auction_one_auction_close_time := intraday_auction_one_auction_close_time_value; intraday_auction_two_start_time := intraday_auction_two_start_time_value; intraday_auction_two_auction_close_time := intraday_auction_two_auction_close_time_value; intraday_auction_three_start_time := intraday_auction_three_start_time_value; intraday_auction_three_auction_close_time := intraday_auction_three_auction_close_time_value; overnight_admin_open_time := overnight_admin_open_time_value; overnight_admin_close_time := overnight_admin_close_time_value; admin_period_close_time := admin_period_close_time_value; unused_8 := unused_8_value; pre_open_order_entry_open_time := pre_open_order_entry_open_time_value; pre_open_order_entry_close_time := pre_open_order_entry_close_time_value; second_unused_8 := second_unused_8_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 144.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !TradingSessionName.encode_length, !OpeningAuctionStartTime.encode_length, !OpeningAuctionCloseTime.encode_length, !ClosingAuctionStartTime.encode_length, !ClosingAuctionCloseTime.encode_length, !ContractOpenTime.encode_length, !ContractCloseTime.encode_length, !IntradayAuctionOneStartTime.encode_length, !IntradayAuctionOneAuctionCloseTime.encode_length, !IntradayAuctionTwoStartTime.encode_length, !IntradayAuctionTwoAuctionCloseTime.encode_length, !IntradayAuctionThreeStartTime.encode_length, !IntradayAuctionThreeAuctionCloseTime.encode_length, !OvernightAdminOpenTime.encode_length, !OvernightAdminCloseTime.encode_length, !AdminPeriodCloseTime.encode_length, !encode_bytes_length, !PreOpenOrderEntryOpenTime.encode_length, !PreOpenOrderEntryCloseTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite TradingSessionName.decode_encode by exact bound_1.
      rewrite OpeningAuctionStartTime.decode_encode by exact bound_2.
      rewrite OpeningAuctionCloseTime.decode_encode by exact bound_3.
      rewrite ClosingAuctionStartTime.decode_encode by exact bound_4.
      rewrite ClosingAuctionCloseTime.decode_encode by exact bound_5.
      rewrite ContractOpenTime.decode_encode by exact bound_6.
      rewrite ContractCloseTime.decode_encode by exact bound_7.
      rewrite IntradayAuctionOneStartTime.decode_encode by exact bound_8.
      rewrite IntradayAuctionOneAuctionCloseTime.decode_encode by exact bound_9.
      rewrite IntradayAuctionTwoStartTime.decode_encode by exact bound_10.
      rewrite IntradayAuctionTwoAuctionCloseTime.decode_encode by exact bound_11.
      rewrite IntradayAuctionThreeStartTime.decode_encode by exact bound_12.
      rewrite IntradayAuctionThreeAuctionCloseTime.decode_encode by exact bound_13.
      rewrite OvernightAdminOpenTime.decode_encode by exact bound_14.
      rewrite OvernightAdminCloseTime.decode_encode by exact bound_15.
      rewrite AdminPeriodCloseTime.decode_encode by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite PreOpenOrderEntryOpenTime.decode_encode by exact bound_18.
      rewrite PreOpenOrderEntryCloseTime.decode_encode by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TradingSessionName.eq_dec | apply OpeningAuctionStartTime.eq_dec | apply OpeningAuctionCloseTime.eq_dec | apply ClosingAuctionStartTime.eq_dec | apply ClosingAuctionCloseTime.eq_dec | apply ContractOpenTime.eq_dec | apply ContractCloseTime.eq_dec | apply IntradayAuctionOneStartTime.eq_dec | apply IntradayAuctionOneAuctionCloseTime.eq_dec | apply IntradayAuctionTwoStartTime.eq_dec | apply IntradayAuctionTwoAuctionCloseTime.eq_dec | apply IntradayAuctionThreeStartTime.eq_dec | apply IntradayAuctionThreeAuctionCloseTime.eq_dec | apply OvernightAdminOpenTime.eq_dec | apply OvernightAdminCloseTime.eq_dec | apply AdminPeriodCloseTime.eq_dec | apply PreOpenOrderEntryOpenTime.eq_dec | apply PreOpenOrderEntryCloseTime.eq_dec]. Defined.

  End TradingSessions.

  Module UpdateTime.

    (** Update Time *)
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

  End UpdateTime.

  Module UpdateDate.

    (** Update Date *)
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

  End UpdateDate.

  Module IndicesPriceData.

    (** Indices Price Data *)
    Record t := {
      indices_sequence : N;
      opening_price : N;
      index_price : N;
      update_time : UpdateTime.t;
      update_date : UpdateDate.t;
      market_capitalisation : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (indices_sequence record < 256 ^ N.of_nat 4)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (index_price record < 256 ^ N.of_nat 8)%N /\
      UpdateTime.bounded (update_time record) /\
      UpdateDate.bounded (update_date record) /\
      (market_capitalisation record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (indices_sequence record) ++
      encode_uint_le 8 (opening_price record) ++
      encode_uint_le 8 (index_price record) ++
      UpdateTime.encode (update_time record) ++
      UpdateDate.encode (update_date record) ++
      encode_uint_le 8 (market_capitalisation record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (indices_sequence_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (opening_price_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (index_price_value, bytes) =>
                  match UpdateTime.decode bytes with
                  | None => None
                  | Some (update_time_value, bytes) =>
                      match UpdateDate.decode bytes with
                      | None => None
                      | Some (update_date_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (market_capitalisation_value, bytes) =>
                              Some ({| indices_sequence := indices_sequence_value; opening_price := opening_price_value; index_price := index_price_value; update_time := update_time_value; update_date := update_date_value; market_capitalisation := market_capitalisation_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !UpdateTime.encode_length, !UpdateDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite UpdateTime.decode_encode by exact bound_3.
      rewrite UpdateDate.decode_encode by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply UpdateTime.eq_dec | apply UpdateDate.eq_dec]. Defined.

  End IndicesPriceData.

  Module IndicesCode.

    (** Indicates the short code for this index. *)
    Record t := {
      indices_code_length_byte : N;
      indices_code_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (indices_code_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (indices_code_characters record) = 19.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (indices_code_length_byte record) ++
      encode_bytes 19 (indices_code_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (indices_code_length_byte_value, bytes) =>
          match decode_bytes 19 bytes with
          | None => None
          | Some (indices_code_characters_value, bytes) =>
              Some ({| indices_code_length_byte := indices_code_length_byte_value; indices_code_characters := indices_code_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End IndicesCode.

  Module IndicesDescription.

    (** Provides a description for the index. *)
    Record t := {
      indices_description_length_byte : N;
      indices_description_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (indices_description_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (indices_description_characters record) = 49.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (indices_description_length_byte record) ++
      encode_bytes 49 (indices_description_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (indices_description_length_byte_value, bytes) =>
          match decode_bytes 49 bytes with
          | None => None
          | Some (indices_description_characters_value, bytes) =>
              Some ({| indices_description_length_byte := indices_description_length_byte_value; indices_description_characters := indices_description_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End IndicesDescription.

  Module IndicesData.

    (** Indices Data *)
    Record t := {
      indices_sequence : N;
      indices_code : IndicesCode.t;
      indices_description : IndicesDescription.t;
      classification : Classification.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (indices_sequence record < 256 ^ N.of_nat 4)%N /\
      IndicesCode.bounded (indices_code record) /\
      IndicesDescription.bounded (indices_description record) /\
      Classification.bounded (classification record).

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (indices_sequence record) ++
      IndicesCode.encode (indices_code record) ++
      IndicesDescription.encode (indices_description record) ++
      Classification.encode (classification record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (indices_sequence_value, bytes) =>
          match IndicesCode.decode bytes with
          | None => None
          | Some (indices_code_value, bytes) =>
              match IndicesDescription.decode bytes with
              | None => None
              | Some (indices_description_value, bytes) =>
                  match Classification.decode bytes with
                  | None => None
                  | Some (classification_value, bytes) =>
                      Some ({| indices_sequence := indices_sequence_value; indices_code := indices_code_value; indices_description := indices_description_value; classification := classification_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 104.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !IndicesCode.encode_length, !IndicesDescription.encode_length, !Classification.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite IndicesCode.decode_encode by exact bound_1.
      rewrite IndicesDescription.decode_encode by exact bound_2.
      rewrite Classification.decode_encode by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply IndicesCode.eq_dec | apply IndicesDescription.eq_dec | apply Classification.eq_dec]. Defined.

  End IndicesData.

  Module SharesInIssueData.

    (** Shares in Issue Data *)
    Record t := {
      shares_in_issue_sequence : N;
      instrument_sequence : N;
      balance : N;
      current_value : N;
      previous_balance : N;
      previous_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (shares_in_issue_sequence record < 256 ^ N.of_nat 4)%N /\
      (instrument_sequence record < 256 ^ N.of_nat 4)%N /\
      (balance record < 256 ^ N.of_nat 8)%N /\
      (current_value record < 256 ^ N.of_nat 8)%N /\
      (previous_balance record < 256 ^ N.of_nat 8)%N /\
      (previous_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (shares_in_issue_sequence record) ++
      encode_uint_le 4 (instrument_sequence record) ++
      encode_uint_le 8 (balance record) ++
      encode_uint_le 8 (current_value record) ++
      encode_uint_le 8 (previous_balance record) ++
      encode_uint_le 8 (previous_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (shares_in_issue_sequence_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_sequence_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (balance_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (current_value_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (previous_balance_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (previous_value_value, bytes) =>
                              Some ({| shares_in_issue_sequence := shares_in_issue_sequence_value; instrument_sequence := instrument_sequence_value; balance := balance_value; current_value := current_value_value; previous_balance := previous_balance_value; previous_value := previous_value_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SharesInIssueData.

  Module TradeDate.

    (** Trade Date *)
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

  End TradeDate.

  Module IndexData.

    (** Index Data *)
    Record t := {
      index_data_sequence : N;
      indices_sequence : N;
      trade_date : TradeDate.t;
      index_value : N;
      market_capitalization : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (index_data_sequence record < 256 ^ N.of_nat 4)%N /\
      (indices_sequence record < 256 ^ N.of_nat 4)%N /\
      TradeDate.bounded (trade_date record) /\
      (index_value record < 256 ^ N.of_nat 8)%N /\
      (market_capitalization record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (index_data_sequence record) ++
      encode_uint_le 4 (indices_sequence record) ++
      TradeDate.encode (trade_date record) ++
      encode_uint_le 8 (index_value record) ++
      encode_uint_le 8 (market_capitalization record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (index_data_sequence_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (indices_sequence_value, bytes) =>
              match TradeDate.decode bytes with
              | None => None
              | Some (trade_date_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (index_value_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (market_capitalization_value, bytes) =>
                          Some ({| index_data_sequence := index_data_sequence_value; indices_sequence := indices_sequence_value; trade_date := trade_date_value; index_value := index_value_value; market_capitalization := market_capitalization_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !TradeDate.encode_length. reflexivity.
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
      rewrite TradeDate.decode_encode by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply TradeDate.eq_dec]. Defined.

  End IndexData.

  Module IndexConstituentsData.

    (** Index Constituents Data *)
    Record t := {
      index_instrument_sequence : N;
      indices_sequence : N;
      instrument_sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (index_instrument_sequence record < 256 ^ N.of_nat 4)%N /\
      (indices_sequence record < 256 ^ N.of_nat 4)%N /\
      (instrument_sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (index_instrument_sequence record) ++
      encode_uint_le 4 (indices_sequence record) ++
      encode_uint_le 4 (instrument_sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (index_instrument_sequence_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (indices_sequence_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (instrument_sequence_value, bytes) =>
                  Some ({| index_instrument_sequence := index_instrument_sequence_value; indices_sequence := indices_sequence_value; instrument_sequence := instrument_sequence_value |}, bytes)
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

  End IndexConstituentsData.

  Module SecondaryExpiryDate.

    (** Secondary Expiry Date *)
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

  End SecondaryExpiryDate.

  Module OrderContract.

    (** Order Contract *)
    Record t := {
      identifier_prefix_b_4 : N;
      expiry_date : ExpiryDate.t;
      instrument_name_b_5 : N;
      strike : N;
      call_put_b_1 : N;
      secondary_expiry_date : SecondaryExpiryDate.t;
      secondary_instrument_name_b_5 : N;
      is_delta_option : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (identifier_prefix_b_4 record < 256 ^ N.of_nat 4)%N /\
      ExpiryDate.bounded (expiry_date record) /\
      (instrument_name_b_5 record < 256 ^ N.of_nat 5)%N /\
      (strike record < 256 ^ N.of_nat 8)%N /\
      (call_put_b_1 record < 256 ^ N.of_nat 1)%N /\
      SecondaryExpiryDate.bounded (secondary_expiry_date record) /\
      (secondary_instrument_name_b_5 record < 256 ^ N.of_nat 5)%N /\
      (is_delta_option record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (identifier_prefix_b_4 record) ++
      ExpiryDate.encode (expiry_date record) ++
      encode_uint 5 (instrument_name_b_5 record) ++
      encode_uint_le 8 (strike record) ++
      encode_uint 1 (call_put_b_1 record) ++
      SecondaryExpiryDate.encode (secondary_expiry_date record) ++
      encode_uint 5 (secondary_instrument_name_b_5 record) ++
      encode_uint 1 (is_delta_option record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (identifier_prefix_b_4_value, bytes) =>
          match ExpiryDate.decode bytes with
          | None => None
          | Some (expiry_date_value, bytes) =>
              match decode_uint 5 bytes with
              | None => None
              | Some (instrument_name_b_5_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (strike_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (call_put_b_1_value, bytes) =>
                          match SecondaryExpiryDate.decode bytes with
                          | None => None
                          | Some (secondary_expiry_date_value, bytes) =>
                              match decode_uint 5 bytes with
                              | None => None
                              | Some (secondary_instrument_name_b_5_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (is_delta_option_value, bytes) =>
                                      Some ({| identifier_prefix_b_4 := identifier_prefix_b_4_value; expiry_date := expiry_date_value; instrument_name_b_5 := instrument_name_b_5_value; strike := strike_value; call_put_b_1 := call_put_b_1_value; secondary_expiry_date := secondary_expiry_date_value; secondary_instrument_name_b_5 := secondary_instrument_name_b_5_value; is_delta_option := is_delta_option_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !ExpiryDate.encode_length, !encode_uint_le_length, !SecondaryExpiryDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite ExpiryDate.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite SecondaryExpiryDate.decode_encode by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply ExpiryDate.eq_dec | apply SecondaryExpiryDate.eq_dec]. Defined.

  End OrderContract.

  Module CompletedTradeMessage.

    (** Sent when an order has been matched or trading has occurred between two parties. *)
    Record t := {
      order_contract : OrderContract.t;
      sequence_number : N;
      price : N;
      quantity_d_8 : N;
      open_price : N;
      previous_closing_price : N;
      closing_price : N;
      change : N;
      open_interest : N;
      low : N;
      high : N;
      day_volume : N;
      vwap : N;
      trade_type : N;
      trade_date : TradeDate.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OrderContract.bounded (order_contract record) /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity_d_8 record < 256 ^ N.of_nat 8)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (previous_closing_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      (change record < 256 ^ N.of_nat 8)%N /\
      (open_interest record < 256 ^ N.of_nat 8)%N /\
      (low record < 256 ^ N.of_nat 8)%N /\
      (high record < 256 ^ N.of_nat 8)%N /\
      (day_volume record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (trade_type record < 256 ^ N.of_nat 4)%N /\
      TradeDate.bounded (trade_date record).

    Definition encode (record : t) : list byte :=
      OrderContract.encode (order_contract record) ++
      encode_uint_le 4 (sequence_number record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 8 (quantity_d_8 record) ++
      encode_uint_le 8 (open_price record) ++
      encode_uint_le 8 (previous_closing_price record) ++
      encode_uint_le 8 (closing_price record) ++
      encode_uint_le 8 (change record) ++
      encode_uint_le 8 (open_interest record) ++
      encode_uint_le 8 (low record) ++
      encode_uint_le 8 (high record) ++
      encode_uint_le 8 (day_volume record) ++
      encode_uint_le 8 (vwap record) ++
      encode_uint_le 4 (trade_type record) ++
      TradeDate.encode (trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OrderContract.decode bytes with
      | None => None
      | Some (order_contract_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (quantity_d_8_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (open_price_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (previous_closing_price_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (closing_price_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (change_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (open_interest_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (low_value, bytes) =>
                                              match decode_uint_le 8 bytes with
                                              | None => None
                                              | Some (high_value, bytes) =>
                                                  match decode_uint_le 8 bytes with
                                                  | None => None
                                                  | Some (day_volume_value, bytes) =>
                                                      match decode_uint_le 8 bytes with
                                                      | None => None
                                                      | Some (vwap_value, bytes) =>
                                                          match decode_uint_le 4 bytes with
                                                          | None => None
                                                          | Some (trade_type_value, bytes) =>
                                                              match TradeDate.decode bytes with
                                                              | None => None
                                                              | Some (trade_date_value, bytes) =>
                                                                  Some ({| order_contract := order_contract_value; sequence_number := sequence_number_value; price := price_value; quantity_d_8 := quantity_d_8_value; open_price := open_price_value; previous_closing_price := previous_closing_price_value; closing_price := closing_price_value; change := change_value; open_interest := open_interest_value; low := low_value; high := high_value; day_volume := day_volume_value; vwap := vwap_value; trade_type := trade_type_value; trade_date := trade_date_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 156.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OrderContract.encode_length, !encode_uint_le_length, !TradeDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OrderContract.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite TradeDate.decode_encode by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply OrderContract.eq_dec | apply TradeDate.eq_dec]. Defined.

  End CompletedTradeMessage.

  Module LastDealtTime.

    (** Last Dealt Time *)
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

  End LastDealtTime.

  Module Display.

    (** Display *)
    Record t := {
      trading_anonymous : N;
      contract : Contract.t;
      mid_price : N;
      last_dealt_price : N;
      last_dealt_time : LastDealtTime.t;
      deal_volume : N;
      high_price : N;
      low_price : N;
      days_volume_i_8 : N;
      last_order_qty : N;
      last_order_buy_sell : list byte;
      last_order_price : N;
      number_of_depth : N;
      open_interest : N;
      change : N;
      auction : N;
      contract_status : N;
      odd_lot : N;
      last_traded_quantity : N;
      date_sequence : N;
      secondary_contract_date_sequence : N;
      strike_sequence : N;
      market_shard_global_sequence_number : N;
      stack_sequence_number : N;
      unused_21 : list byte;
      update_time : UpdateTime.t;
      vwap : N;
      closing_price : N;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trading_anonymous record < 256 ^ N.of_nat 1)%N /\
      Contract.bounded (contract record) /\
      (mid_price record < 256 ^ N.of_nat 8)%N /\
      (last_dealt_price record < 256 ^ N.of_nat 8)%N /\
      LastDealtTime.bounded (last_dealt_time record) /\
      (deal_volume record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (days_volume_i_8 record < 256 ^ N.of_nat 8)%N /\
      (last_order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (last_order_buy_sell record) = 1 /\
      (last_order_price record < 256 ^ N.of_nat 8)%N /\
      (number_of_depth record < 256 ^ N.of_nat 1)%N /\
      (open_interest record < 256 ^ N.of_nat 8)%N /\
      (change record < 256 ^ N.of_nat 8)%N /\
      (auction record < 256 ^ N.of_nat 1)%N /\
      (contract_status record < 256 ^ N.of_nat 1)%N /\
      (odd_lot record < 256 ^ N.of_nat 1)%N /\
      (last_traded_quantity record < 256 ^ N.of_nat 8)%N /\
      (date_sequence record < 256 ^ N.of_nat 4)%N /\
      (secondary_contract_date_sequence record < 256 ^ N.of_nat 4)%N /\
      (strike_sequence record < 256 ^ N.of_nat 4)%N /\
      (market_shard_global_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (stack_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (unused_21 record) = 21 /\
      UpdateTime.bounded (update_time record) /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (trading_anonymous record) ++
      Contract.encode (contract record) ++
      encode_uint_le 8 (mid_price record) ++
      encode_uint_le 8 (last_dealt_price record) ++
      LastDealtTime.encode (last_dealt_time record) ++
      encode_uint_le 8 (deal_volume record) ++
      encode_uint_le 8 (high_price record) ++
      encode_uint_le 8 (low_price record) ++
      encode_uint_le 8 (days_volume_i_8 record) ++
      encode_uint_le 4 (last_order_qty record) ++
      encode_bytes 1 (last_order_buy_sell record) ++
      encode_uint_le 8 (last_order_price record) ++
      encode_uint 1 (number_of_depth record) ++
      encode_uint_le 8 (open_interest record) ++
      encode_uint_le 8 (change record) ++
      encode_uint 1 (auction record) ++
      encode_uint 1 (contract_status record) ++
      encode_uint 1 (odd_lot record) ++
      encode_uint_le 8 (last_traded_quantity record) ++
      encode_uint_le 4 (date_sequence record) ++
      encode_uint_le 4 (secondary_contract_date_sequence record) ++
      encode_uint_le 4 (strike_sequence record) ++
      encode_uint_le 4 (market_shard_global_sequence_number record) ++
      encode_uint_le 4 (stack_sequence_number record) ++
      encode_bytes 21 (unused_21 record) ++
      UpdateTime.encode (update_time record) ++
      encode_uint_le 8 (vwap record) ++
      encode_uint_le 8 (closing_price record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (trading_anonymous_value, bytes) =>
          match Contract.decode bytes with
          | None => None
          | Some (contract_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (mid_price_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (last_dealt_price_value, bytes) =>
                      match LastDealtTime.decode bytes with
                      | None => None
                      | Some (last_dealt_time_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (deal_volume_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (high_price_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (low_price_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (days_volume_i_8_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (last_order_qty_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (last_order_buy_sell_value, bytes) =>
                                                  match decode_uint_le 8 bytes with
                                                  | None => None
                                                  | Some (last_order_price_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (number_of_depth_value, bytes) =>
                                                          match decode_uint_le 8 bytes with
                                                          | None => None
                                                          | Some (open_interest_value, bytes) =>
                                                              match decode_uint_le 8 bytes with
                                                              | None => None
                                                              | Some (change_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (auction_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (contract_status_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (odd_lot_value, bytes) =>
                                                                              match decode_uint_le 8 bytes with
                                                                              | None => None
                                                                              | Some (last_traded_quantity_value, bytes) =>
                                                                                  match decode_uint_le 4 bytes with
                                                                                  | None => None
                                                                                  | Some (date_sequence_value, bytes) =>
                                                                                      match decode_uint_le 4 bytes with
                                                                                      | None => None
                                                                                      | Some (secondary_contract_date_sequence_value, bytes) =>
                                                                                          match decode_uint_le 4 bytes with
                                                                                          | None => None
                                                                                          | Some (strike_sequence_value, bytes) =>
                                                                                              match decode_uint_le 4 bytes with
                                                                                              | None => None
                                                                                              | Some (market_shard_global_sequence_number_value, bytes) =>
                                                                                                  match decode_uint_le 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (stack_sequence_number_value, bytes) =>
                                                                                                      match decode_bytes 21 bytes with
                                                                                                      | None => None
                                                                                                      | Some (unused_21_value, bytes) =>
                                                                                                          match UpdateTime.decode bytes with
                                                                                                          | None => None
                                                                                                          | Some (update_time_value, bytes) =>
                                                                                                              match decode_uint_le 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (vwap_value, bytes) =>
                                                                                                                  match decode_uint_le 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (closing_price_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (reserved_1_value, bytes) =>
                                                                                                                          Some ({| trading_anonymous := trading_anonymous_value; contract := contract_value; mid_price := mid_price_value; last_dealt_price := last_dealt_price_value; last_dealt_time := last_dealt_time_value; deal_volume := deal_volume_value; high_price := high_price_value; low_price := low_price_value; days_volume_i_8 := days_volume_i_8_value; last_order_qty := last_order_qty_value; last_order_buy_sell := last_order_buy_sell_value; last_order_price := last_order_price_value; number_of_depth := number_of_depth_value; open_interest := open_interest_value; change := change_value; auction := auction_value; contract_status := contract_status_value; odd_lot := odd_lot_value; last_traded_quantity := last_traded_quantity_value; date_sequence := date_sequence_value; secondary_contract_date_sequence := secondary_contract_date_sequence_value; strike_sequence := strike_sequence_value; market_shard_global_sequence_number := market_shard_global_sequence_number_value; stack_sequence_number := stack_sequence_number_value; unused_21 := unused_21_value; update_time := update_time_value; vwap := vwap_value; closing_price := closing_price_value; reserved_1 := reserved_1_value |}, bytes)
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
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 204.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !Contract.encode_length, !encode_uint_le_length, !LastDealtTime.encode_length, !encode_bytes_length, !UpdateTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 bound_28]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite Contract.decode_encode by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite LastDealtTime.decode_encode by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint_le by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint_le by exact bound_18.
      rewrite decode_encode_uint_le by exact bound_19.
      rewrite decode_encode_uint_le by exact bound_20.
      rewrite decode_encode_uint_le by exact bound_21.
      rewrite decode_encode_uint_le by exact bound_22.
      rewrite decode_encode_uint_le by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite UpdateTime.decode_encode by exact bound_25.
      rewrite decode_encode_uint_le by exact bound_26.
      rewrite decode_encode_uint_le by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Contract.eq_dec | apply LastDealtTime.eq_dec | apply UpdateTime.eq_dec]. Defined.

  End Display.

  Module BuyWhoMember.

    (** Member bidding *)
    Record t := {
      buy_who_length_byte : N;
      buy_who_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (buy_who_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_who_characters record) = 5.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (buy_who_length_byte record) ++
      encode_bytes 5 (buy_who_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (buy_who_length_byte_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (buy_who_characters_value, bytes) =>
              Some ({| buy_who_length_byte := buy_who_length_byte_value; buy_who_characters := buy_who_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End BuyWhoMember.

  Module BuyWhoUniqueMember.

    (** Anonymous contract: length byte 0, then the unique member number *)
    Record t := {
      buy_who_length_byte : N;
      unique_member_number : N;
      unused_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (buy_who_length_byte record < 256 ^ N.of_nat 1)%N /\
      (unique_member_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (unused_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (buy_who_length_byte record) ++
      encode_uint_le 4 (unique_member_number record) ++
      encode_bytes 1 (unused_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (buy_who_length_byte_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (unique_member_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (unused_1_value, bytes) =>
                  Some ({| buy_who_length_byte := buy_who_length_byte_value; unique_member_number := unique_member_number_value; unused_1 := unused_1_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_uint_le_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BuyWhoUniqueMember.

  Module SellWhoMember.

    (** Member asking *)
    Record t := {
      sell_who_length_byte : N;
      sell_who_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sell_who_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (sell_who_characters record) = 5.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (sell_who_length_byte record) ++
      encode_bytes 5 (sell_who_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (sell_who_length_byte_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (sell_who_characters_value, bytes) =>
              Some ({| sell_who_length_byte := sell_who_length_byte_value; sell_who_characters := sell_who_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End SellWhoMember.

  Module SellWhoUniqueMember.

    (** Anonymous contract: length byte 0, then the unique member number *)
    Record t := {
      sell_who_length_byte : N;
      unique_member_number : N;
      unused_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sell_who_length_byte record < 256 ^ N.of_nat 1)%N /\
      (unique_member_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (unused_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (sell_who_length_byte record) ++
      encode_uint_le 4 (unique_member_number record) ++
      encode_bytes 1 (unused_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (sell_who_length_byte_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (unique_member_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (unused_1_value, bytes) =>
                  Some ({| sell_who_length_byte := sell_who_length_byte_value; unique_member_number := unique_member_number_value; unused_1 := unused_1_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_uint_le_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SellWhoUniqueMember.

  Module IndexSequenceNumber.

    (** Indicates the sequence number of the index. *)
    Record t := {
      index_sequence_number_length_byte : N;
      index_sequence_number_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (index_sequence_number_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (index_sequence_number_characters record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (index_sequence_number_length_byte record) ++
      encode_bytes 3 (index_sequence_number_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (index_sequence_number_length_byte_value, bytes) =>
          match decode_bytes 3 bytes with
          | None => None
          | Some (index_sequence_number_characters_value, bytes) =>
              Some ({| index_sequence_number_length_byte := index_sequence_number_length_byte_value; index_sequence_number_characters := index_sequence_number_characters_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexSequenceNumber.

  Module IndicesMessage.

    (** Each Index will be sent in this format. *)
    Record t := {
      index_sequence_number : IndexSequenceNumber.t;
      opening_price : N;
      index_price : N;
      update_time : UpdateTime.t;
      update_date : UpdateDate.t;
      market_capitalisation : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IndexSequenceNumber.bounded (index_sequence_number record) /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (index_price record < 256 ^ N.of_nat 8)%N /\
      UpdateTime.bounded (update_time record) /\
      UpdateDate.bounded (update_date record) /\
      (market_capitalisation record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      IndexSequenceNumber.encode (index_sequence_number record) ++
      encode_uint_le 8 (opening_price record) ++
      encode_uint_le 8 (index_price record) ++
      UpdateTime.encode (update_time record) ++
      UpdateDate.encode (update_date record) ++
      encode_uint_le 8 (market_capitalisation record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IndexSequenceNumber.decode bytes with
      | None => None
      | Some (index_sequence_number_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (opening_price_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (index_price_value, bytes) =>
                  match UpdateTime.decode bytes with
                  | None => None
                  | Some (update_time_value, bytes) =>
                      match UpdateDate.decode bytes with
                      | None => None
                      | Some (update_date_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (market_capitalisation_value, bytes) =>
                              Some ({| index_sequence_number := index_sequence_number_value; opening_price := opening_price_value; index_price := index_price_value; update_time := update_time_value; update_date := update_date_value; market_capitalisation := market_capitalisation_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IndexSequenceNumber.encode_length, !encode_uint_le_length, !UpdateTime.encode_length, !UpdateDate.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IndexSequenceNumber.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite UpdateTime.decode_encode by exact bound_3.
      rewrite UpdateDate.decode_encode by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply IndexSequenceNumber.eq_dec | apply UpdateTime.eq_dec | apply UpdateDate.eq_dec]. Defined.

  End IndicesMessage.

  Module MessageP250.

    (** A Description of the error. *)
    Record t := {
      message_p_250_length_byte : N;
      message_p_250_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_p_250_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (message_p_250_characters record) = 249.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_p_250_length_byte record) ++
      encode_bytes 249 (message_p_250_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_p_250_length_byte_value, bytes) =>
          match decode_bytes 249 bytes with
          | None => None
          | Some (message_p_250_characters_value, bytes) =>
              Some ({| message_p_250_length_byte := message_p_250_length_byte_value; message_p_250_characters := message_p_250_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 250.
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

  End MessageP250.

  Module ExchangeAnnouncementsMessage.

    (** Error and information messages. *)
    Record t := {
      market_number_i_4 : N;
      market_shard_number_i_4 : N;
      error_number : N;
      information_or_error_indicator : N;
      message_p_250 : MessageP250.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_number_i_4 record < 256 ^ N.of_nat 4)%N /\
      (market_shard_number_i_4 record < 256 ^ N.of_nat 4)%N /\
      (error_number record < 256 ^ N.of_nat 4)%N /\
      (information_or_error_indicator record < 256 ^ N.of_nat 1)%N /\
      MessageP250.bounded (message_p_250 record).

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (market_number_i_4 record) ++
      encode_uint_le 4 (market_shard_number_i_4 record) ++
      encode_uint_le 4 (error_number record) ++
      encode_uint 1 (information_or_error_indicator record) ++
      MessageP250.encode (message_p_250 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (market_number_i_4_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (market_shard_number_i_4_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (error_number_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (information_or_error_indicator_value, bytes) =>
                      match MessageP250.decode bytes with
                      | None => None
                      | Some (message_p_250_value, bytes) =>
                          Some ({| market_number_i_4 := market_number_i_4_value; market_shard_number_i_4 := market_shard_number_i_4_value; error_number := error_number_value; information_or_error_indicator := information_or_error_indicator_value; message_p_250 := message_p_250_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 263.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !MessageP250.encode_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite MessageP250.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageP250.eq_dec]. Defined.

  End ExchangeAnnouncementsMessage.

  Module NotificationOfFailureMessage.

    (** Sent on the failure or the recovery of the exchange trading system. *)
    Record t := {
      failure_notice_identifier : N;
      market_number_i_4 : N;
      market_shard_number_i_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (failure_notice_identifier record < 256 ^ N.of_nat 4)%N /\
      (market_number_i_4 record < 256 ^ N.of_nat 4)%N /\
      (market_shard_number_i_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (failure_notice_identifier record) ++
      encode_uint_le 4 (market_number_i_4 record) ++
      encode_uint_le 4 (market_shard_number_i_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (failure_notice_identifier_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (market_number_i_4_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (market_shard_number_i_4_value, bytes) =>
                  Some ({| failure_notice_identifier := failure_notice_identifier_value; market_number_i_4 := market_number_i_4_value; market_shard_number_i_4 := market_shard_number_i_4_value |}, bytes)
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

  End NotificationOfFailureMessage.

  Module ReferenceMessageType.

    (** Indicates the message type of the incoming message this reject is in response to. *)
    Record t := {
      reference_message_type_length_byte : N;
      reference_message_type_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reference_message_type_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference_message_type_characters record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (reference_message_type_length_byte record) ++
      encode_bytes 2 (reference_message_type_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (reference_message_type_length_byte_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (reference_message_type_characters_value, bytes) =>
              Some ({| reference_message_type_length_byte := reference_message_type_length_byte_value; reference_message_type_characters := reference_message_type_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End ReferenceMessageType.

  Module TextP250.

    (** The text of the rejection message. *)
    Record t := {
      text_p_250_length_byte : N;
      text_p_250_characters : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (text_p_250_length_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (text_p_250_characters record) = 249.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (text_p_250_length_byte record) ++
      encode_bytes 249 (text_p_250_characters record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (text_p_250_length_byte_value, bytes) =>
          match decode_bytes 249 bytes with
          | None => None
          | Some (text_p_250_characters_value, bytes) =>
              Some ({| text_p_250_length_byte := text_p_250_length_byte_value; text_p_250_characters := text_p_250_characters_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 250.
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

  End TextP250.

  Module BusinessMessageRejectMessage.

    (** Returned in response to an incoming message to indicate a failure to process this message for some business validation failure. *)
    Record t := {
      reference_sequence_number : N;
      reference_message_type : ReferenceMessageType.t;
      text_p_250 : TextP250.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reference_sequence_number record < 256 ^ N.of_nat 4)%N /\
      ReferenceMessageType.bounded (reference_message_type record) /\
      TextP250.bounded (text_p_250 record).

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (reference_sequence_number record) ++
      ReferenceMessageType.encode (reference_message_type record) ++
      TextP250.encode (text_p_250 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (reference_sequence_number_value, bytes) =>
          match ReferenceMessageType.decode bytes with
          | None => None
          | Some (reference_message_type_value, bytes) =>
              match TextP250.decode bytes with
              | None => None
              | Some (text_p_250_value, bytes) =>
                  Some ({| reference_sequence_number := reference_sequence_number_value; reference_message_type := reference_message_type_value; text_p_250 := text_p_250_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 257.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !ReferenceMessageType.encode_length, !TextP250.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite ReferenceMessageType.decode_encode by exact bound_1.
      rewrite TextP250.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply ReferenceMessageType.eq_dec | apply TextP250.eq_dec]. Defined.

  End BusinessMessageRejectMessage.

End NairobiBondsMarketDataV214Server.
