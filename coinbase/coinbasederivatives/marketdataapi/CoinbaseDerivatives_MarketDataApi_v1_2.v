From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Coinbase Market Data Api

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
      - a block whose stated length holds more than its fields
  *)

Module CoinbaseDerivativesMarketDataApiV12.

  Module MessageHeader.

    (** Coinbase Sbe Market Data message header — frame length plus standard SBE header *)
    Record t := {
      frame_length : N;
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (frame_length record < 256 ^ N.of_nat 2)%N /\
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 2)%N /\
      (schema_id record < 256 ^ N.of_nat 2)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (frame_length record) ++
      encode_uint 2 (block_length record) ++
      encode_uint 2 (template_id record) ++
      encode_uint 2 (schema_id record) ++
      encode_uint 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (frame_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (block_length_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (template_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (schema_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (version_value, bytes) =>
                          Some ({| frame_length := frame_length_value; block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End MessageHeader.

  Module InstrHeader.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader.

  Module InstrHeader2.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader2.

  Module InstrHeader3.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader3.

  Module InstrHeader4.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader4.

  Module InstrHeader5.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader5.

  Module InstrHeader6.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader6.

  Module InstrHeader7.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader7.

  Module InstrHeader8.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader8.

  Module InstrHeader9.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader9.

  Module InstrHeader10.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader10.

  Module InstrHeader11.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader11.

  Module InstrHeader12.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader12.

  Module InstrHeader13.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader13.

  Module InstrHeader14.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (instr_seq_num record) ++
      encode_uint 2 (trading_session_date record) ++
      encode_uint 2 (reserved record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader14.

End CoinbaseDerivativesMarketDataApiV12.
