From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Multicast Latency Feed

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
      - the dispatch that chooses a message by its type
      - a run filling what frames it
  *)

Module CboeEuropeLatencyFeedV14.

  Module PacketHeader.

    Record t := {
      length_ : N;
      message_count : N;
      unit_ : N;
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      (unit_ record < 256 ^ N.of_nat 1)%N /\
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_uint 1 (unit_ record) ++
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (unit__value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; unit_ := unit__value; sequence := sequence_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 1)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  Module LatencyStatMessage.

    (** A Latency Stat Message demonstrates performance for a specific Matching Engine unit for a specific timeframe *)
    Record t := {
      measurement_type : N;
      matching_unit : N;
      begin_time : N;
      end_time : N;
      count : N;
      minimum : N;
      maximum : N;
      average : N;
      standard_deviation : N;
      mode : N;
      percentile_99_point_9 : N;
      percentile_99 : N;
      percentile_95 : N;
      percentile_90 : N;
      percentile_75 : N;
      percentile_50 : N;
      percentile_25 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (measurement_type record < 256 ^ N.of_nat 1)%N /\
      (matching_unit record < 256 ^ N.of_nat 1)%N /\
      (begin_time record < 256 ^ N.of_nat 4)%N /\
      (end_time record < 256 ^ N.of_nat 4)%N /\
      (count record < 256 ^ N.of_nat 4)%N /\
      (minimum record < 256 ^ N.of_nat 8)%N /\
      (maximum record < 256 ^ N.of_nat 8)%N /\
      (average record < 256 ^ N.of_nat 8)%N /\
      (standard_deviation record < 256 ^ N.of_nat 8)%N /\
      (mode record < 256 ^ N.of_nat 8)%N /\
      (percentile_99_point_9 record < 256 ^ N.of_nat 8)%N /\
      (percentile_99 record < 256 ^ N.of_nat 8)%N /\
      (percentile_95 record < 256 ^ N.of_nat 8)%N /\
      (percentile_90 record < 256 ^ N.of_nat 8)%N /\
      (percentile_75 record < 256 ^ N.of_nat 8)%N /\
      (percentile_50 record < 256 ^ N.of_nat 8)%N /\
      (percentile_25 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (measurement_type record) ++
      encode_uint 1 (matching_unit record) ++
      encode_uint 4 (begin_time record) ++
      encode_uint 4 (end_time record) ++
      encode_uint 4 (count record) ++
      encode_uint 8 (minimum record) ++
      encode_uint 8 (maximum record) ++
      encode_uint 8 (average record) ++
      encode_uint 8 (standard_deviation record) ++
      encode_uint 8 (mode record) ++
      encode_uint 8 (percentile_99_point_9 record) ++
      encode_uint 8 (percentile_99 record) ++
      encode_uint 8 (percentile_95 record) ++
      encode_uint 8 (percentile_90 record) ++
      encode_uint 8 (percentile_75 record) ++
      encode_uint 8 (percentile_50 record) ++
      encode_uint 8 (percentile_25 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (measurement_type_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (matching_unit_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (begin_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (end_time_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (count_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (minimum_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (maximum_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (average_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (standard_deviation_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (mode_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (percentile_99_point_9_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (percentile_99_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (percentile_95_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (percentile_90_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (percentile_75_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (percentile_50_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (percentile_25_value, bytes) =>
                                                                          Some ({| measurement_type := measurement_type_value; matching_unit := matching_unit_value; begin_time := begin_time_value; end_time := end_time_value; count := count_value; minimum := minimum_value; maximum := maximum_value; average := average_value; standard_deviation := standard_deviation_value; mode := mode_value; percentile_99_point_9 := percentile_99_point_9_value; percentile_99 := percentile_99_value; percentile_95 := percentile_95_value; percentile_90 := percentile_90_value; percentile_75 := percentile_75_value; percentile_50 := percentile_50_value; percentile_25 := percentile_25_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 110.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End LatencyStatMessage.

End CboeEuropeLatencyFeedV14.
