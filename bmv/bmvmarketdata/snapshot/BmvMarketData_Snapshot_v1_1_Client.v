From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsa Mexicana de Valores Bmv Market Data Snapshot

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

    License: MIT No Attribution
  *)

Module BmvMarketDataSnapshotV11Client.

  Module ClientMessageHeader.

    (** Request length and message type *)
    Record t := {
      client_length : N;
      client_message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_length record < 256 ^ N.of_nat 1)%N /\
      (client_message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (client_length record) ++
      encode_uint 1 (client_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (client_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (client_message_type_value, bytes) =>
              Some ({| client_length := client_length_value; client_message_type := client_message_type_value |}, bytes)
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

  End ClientMessageHeader.

  Module LoginMessage.

    (** Logs the consumer in to the replay or snapshot channel. *)
    Record t := {
      market_data_group : N;
      user : list byte;
      password : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_data_group record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user record) = 6 /\
      Datatypes.length (password record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (market_data_group record) ++
      encode_bytes 6 (user record) ++
      encode_bytes 10 (password record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (market_data_group_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (user_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (password_value, bytes) =>
                  Some ({| market_data_group := market_data_group_value; user := user_value; password := password_value |}, bytes)
              end
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginMessage.

  Module ReplayRequestMessage.

    (** Requests the replay of messages already published on a multicast group. *)
    Record t := {
      market_data_group : N;
      first_message : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_data_group record < 256 ^ N.of_nat 1)%N /\
      (first_message record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (market_data_group record) ++
      encode_uint 4 (first_message record) ++
      encode_uint 2 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (market_data_group_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (first_message_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  Some ({| market_data_group := market_data_group_value; first_message := first_message_value; quantity := quantity_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End ReplayRequestMessage.

  Module SnapshotRequestMessage.

    (** Requests a snapshot of a multicast group. *)
    Record t := {
      market_data_group : N;
      instrument_id : N;
      snapshot_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_data_group record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (snapshot_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (market_data_group record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (snapshot_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (market_data_group_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (snapshot_type_value, bytes) =>
                  Some ({| market_data_group := market_data_group_value; instrument_id := instrument_id_value; snapshot_type := snapshot_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End SnapshotRequestMessage.

  Module SnapshotIndicesRequestMessage.

    (** Requests a snapshot of an index. *)
    Record t := {
      market_data_group : N;
      component : list byte;
      recovery_hour : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_data_group record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (component record) = 2 /\
      (recovery_hour record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (market_data_group record) ++
      encode_bytes 2 (component record) ++
      encode_uint 8 (recovery_hour record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (market_data_group_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (component_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (recovery_hour_value, bytes) =>
                  Some ({| market_data_group := market_data_group_value; component := component_value; recovery_hour := recovery_hour_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SnapshotIndicesRequestMessage.

  Module SnapshotConsolidatedFeedRequestMessage.

    (** Requests a snapshot of a Consolidated Feed group. *)
    Record t := {
      market_data_group : N;
      instrument_id : N;
      snapshot_type : N;
      origin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_data_group record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (snapshot_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (origin record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (market_data_group record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (snapshot_type record) ++
      encode_bytes 1 (origin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (market_data_group_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (snapshot_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (origin_value, bytes) =>
                      Some ({| market_data_group := market_data_group_value; instrument_id := instrument_id_value; snapshot_type := snapshot_type_value; origin := origin_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End SnapshotConsolidatedFeedRequestMessage.

End BmvMarketDataSnapshotV11Client.
