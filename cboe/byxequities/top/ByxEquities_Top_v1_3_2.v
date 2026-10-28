From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Top

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
  *)

Module ByxEquitiesTopV132.

  Module LogonMessage.

    (** Logon Message *)
    Record t := {
      username : list byte;
      password : list byte;
      spin_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 6 /\
      Datatypes.length (password record) = 10 /\
      Datatypes.length (spin_flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 1 (spin_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (spin_flag_value, bytes) =>
                  Some ({| username := username_value; password := password_value; spin_flag := spin_flag_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonMessage.

  Module LogonRejectedMessage.

    (** Logon Rejected Message *)
    Record t := {
      reject_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reject_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reject_reason_value, bytes) =>
          Some ({| reject_reason := reject_reason_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End LogonRejectedMessage.

  Module SecondsMessage.

    (** Sent for every second for which at least one message is being generated. *)
    Record t := {
      seconds : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (seconds record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          Some ({| seconds := seconds_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End SecondsMessage.

  Module MillisecondsMessage.

    (** Sent for every millisecond for which at least one message is being generated. *)
    Record t := {
      milliseconds : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (milliseconds record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (milliseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (milliseconds_value, bytes) =>
          Some ({| milliseconds := milliseconds_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End MillisecondsMessage.

  Module ExpandedSpinMessage.

    (** Expanded Spin Message *)
    Record t := {
      timestamp : list byte;
      symbol_expanded : list byte;
      bid_price_long : list byte;
      bid_quantity_long : list byte;
      ask_price_long : list byte;
      ask_quantity_long : list byte;
      last_trade_time : list byte;
      last_trade_price : list byte;
      last_trade_size : list byte;
      cumulative_volume_long : list byte;
      halt_status : list byte;
      reg_sho_action : list byte;
      reserved_1 : list byte;
      reserved_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (timestamp record) = 8 /\
      Datatypes.length (symbol_expanded record) = 8 /\
      Datatypes.length (bid_price_long record) = 10 /\
      Datatypes.length (bid_quantity_long record) = 6 /\
      Datatypes.length (ask_price_long record) = 10 /\
      Datatypes.length (ask_quantity_long record) = 6 /\
      Datatypes.length (last_trade_time record) = 8 /\
      Datatypes.length (last_trade_price record) = 10 /\
      Datatypes.length (last_trade_size record) = 6 /\
      Datatypes.length (cumulative_volume_long record) = 9 /\
      Datatypes.length (halt_status record) = 1 /\
      Datatypes.length (reg_sho_action record) = 1 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (reserved_2 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (timestamp record) ++
      encode_bytes 8 (symbol_expanded record) ++
      encode_bytes 10 (bid_price_long record) ++
      encode_bytes 6 (bid_quantity_long record) ++
      encode_bytes 10 (ask_price_long record) ++
      encode_bytes 6 (ask_quantity_long record) ++
      encode_bytes 8 (last_trade_time record) ++
      encode_bytes 10 (last_trade_price record) ++
      encode_bytes 6 (last_trade_size record) ++
      encode_bytes 9 (cumulative_volume_long record) ++
      encode_bytes 1 (halt_status record) ++
      encode_bytes 1 (reg_sho_action record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_expanded_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (bid_price_long_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (bid_quantity_long_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (ask_price_long_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (ask_quantity_long_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (last_trade_time_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (last_trade_price_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (last_trade_size_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (cumulative_volume_long_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (halt_status_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (reg_sho_action_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (reserved_1_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (reserved_2_value, bytes) =>
                                                              Some ({| timestamp := timestamp_value; symbol_expanded := symbol_expanded_value; bid_price_long := bid_price_long_value; bid_quantity_long := bid_quantity_long_value; ask_price_long := ask_price_long_value; ask_quantity_long := ask_quantity_long_value; last_trade_time := last_trade_time_value; last_trade_price := last_trade_price_value; last_trade_size := last_trade_size_value; cumulative_volume_long := cumulative_volume_long_value; halt_status := halt_status_value; reg_sho_action := reg_sho_action_value; reserved_1 := reserved_1_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 85.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedSpinMessage.

  Module ExpandedBidUpdateMessage.

    (** Expanded Bid Update Message *)
    Record t := {
      symbol_expanded : list byte;
      bid_price_long : list byte;
      bid_quantity_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_expanded record) = 8 /\
      Datatypes.length (bid_price_long record) = 10 /\
      Datatypes.length (bid_quantity_long record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (symbol_expanded record) ++
      encode_bytes 10 (bid_price_long record) ++
      encode_bytes 6 (bid_quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (symbol_expanded_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (bid_price_long_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (bid_quantity_long_value, bytes) =>
                  Some ({| symbol_expanded := symbol_expanded_value; bid_price_long := bid_price_long_value; bid_quantity_long := bid_quantity_long_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedBidUpdateMessage.

  Module LongBidUpdateMessage.

    (** Long Bid Update Message *)
    Record t := {
      symbol_long : list byte;
      bid_price_long : list byte;
      bid_quantity_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_long record) = 6 /\
      Datatypes.length (bid_price_long record) = 10 /\
      Datatypes.length (bid_quantity_long record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (symbol_long record) ++
      encode_bytes 10 (bid_price_long record) ++
      encode_bytes 6 (bid_quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (symbol_long_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (bid_price_long_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (bid_quantity_long_value, bytes) =>
                  Some ({| symbol_long := symbol_long_value; bid_price_long := bid_price_long_value; bid_quantity_long := bid_quantity_long_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongBidUpdateMessage.

  Module ShortBidUpdateMessage.

    (** Short Bid Update Message *)
    Record t := {
      symbol_short : list byte;
      bid_price_short : list byte;
      bid_quantity_short : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_short record) = 4 /\
      Datatypes.length (bid_price_short record) = 5 /\
      Datatypes.length (bid_quantity_short record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (symbol_short record) ++
      encode_bytes 5 (bid_price_short record) ++
      encode_bytes 5 (bid_quantity_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (symbol_short_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (bid_price_short_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (bid_quantity_short_value, bytes) =>
                  Some ({| symbol_short := symbol_short_value; bid_price_short := bid_price_short_value; bid_quantity_short := bid_quantity_short_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ShortBidUpdateMessage.

  Module ExpandedAskUpdateMessage.

    (** Expanded Ask Update Message *)
    Record t := {
      symbol_expanded : list byte;
      ask_price_long : list byte;
      ask_quantity_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_expanded record) = 8 /\
      Datatypes.length (ask_price_long record) = 10 /\
      Datatypes.length (ask_quantity_long record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (symbol_expanded record) ++
      encode_bytes 10 (ask_price_long record) ++
      encode_bytes 6 (ask_quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (symbol_expanded_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (ask_price_long_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (ask_quantity_long_value, bytes) =>
                  Some ({| symbol_expanded := symbol_expanded_value; ask_price_long := ask_price_long_value; ask_quantity_long := ask_quantity_long_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedAskUpdateMessage.

  Module LongAskUpdateMessage.

    (** Long Ask Update Message *)
    Record t := {
      symbol_long : list byte;
      ask_price_long : list byte;
      ask_quantity_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_long record) = 6 /\
      Datatypes.length (ask_price_long record) = 10 /\
      Datatypes.length (ask_quantity_long record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (symbol_long record) ++
      encode_bytes 10 (ask_price_long record) ++
      encode_bytes 6 (ask_quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (symbol_long_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (ask_price_long_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (ask_quantity_long_value, bytes) =>
                  Some ({| symbol_long := symbol_long_value; ask_price_long := ask_price_long_value; ask_quantity_long := ask_quantity_long_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongAskUpdateMessage.

  Module ShortAskUpdateMessage.

    (** Short Ask Update Message *)
    Record t := {
      symbol_short : list byte;
      ask_price_short : list byte;
      ask_quantity_short : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_short record) = 4 /\
      Datatypes.length (ask_price_short record) = 5 /\
      Datatypes.length (ask_quantity_short record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (symbol_short record) ++
      encode_bytes 5 (ask_price_short record) ++
      encode_bytes 5 (ask_quantity_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (symbol_short_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (ask_price_short_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (ask_quantity_short_value, bytes) =>
                  Some ({| symbol_short := symbol_short_value; ask_price_short := ask_price_short_value; ask_quantity_short := ask_quantity_short_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ShortAskUpdateMessage.

  Module ExpandedTwoSidedUpdateMessage.

    (** Expanded Two-Sided Update Message *)
    Record t := {
      symbol_expanded : list byte;
      bid_price_long : list byte;
      bid_quantity_long : list byte;
      ask_price_long : list byte;
      ask_quantity_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_expanded record) = 8 /\
      Datatypes.length (bid_price_long record) = 10 /\
      Datatypes.length (bid_quantity_long record) = 6 /\
      Datatypes.length (ask_price_long record) = 10 /\
      Datatypes.length (ask_quantity_long record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (symbol_expanded record) ++
      encode_bytes 10 (bid_price_long record) ++
      encode_bytes 6 (bid_quantity_long record) ++
      encode_bytes 10 (ask_price_long record) ++
      encode_bytes 6 (ask_quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (symbol_expanded_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (bid_price_long_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (bid_quantity_long_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (ask_price_long_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (ask_quantity_long_value, bytes) =>
                          Some ({| symbol_expanded := symbol_expanded_value; bid_price_long := bid_price_long_value; bid_quantity_long := bid_quantity_long_value; ask_price_long := ask_price_long_value; ask_quantity_long := ask_quantity_long_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedTwoSidedUpdateMessage.

  Module LongTwoSidedUpdateMessage.

    (** Long Two-Sided Update Message *)
    Record t := {
      symbol_long : list byte;
      bid_price_long : list byte;
      bid_quantity_long : list byte;
      ask_price_long : list byte;
      ask_quantity_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_long record) = 6 /\
      Datatypes.length (bid_price_long record) = 10 /\
      Datatypes.length (bid_quantity_long record) = 6 /\
      Datatypes.length (ask_price_long record) = 10 /\
      Datatypes.length (ask_quantity_long record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (symbol_long record) ++
      encode_bytes 10 (bid_price_long record) ++
      encode_bytes 6 (bid_quantity_long record) ++
      encode_bytes 10 (ask_price_long record) ++
      encode_bytes 6 (ask_quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (symbol_long_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (bid_price_long_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (bid_quantity_long_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (ask_price_long_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (ask_quantity_long_value, bytes) =>
                          Some ({| symbol_long := symbol_long_value; bid_price_long := bid_price_long_value; bid_quantity_long := bid_quantity_long_value; ask_price_long := ask_price_long_value; ask_quantity_long := ask_quantity_long_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongTwoSidedUpdateMessage.

  Module ShortTwoSidedUpdateMessage.

    (** Short Two-Sided Update Message *)
    Record t := {
      symbol_short : list byte;
      bid_price_short : list byte;
      bid_quantity_short : list byte;
      ask_price_short : list byte;
      ask_quantity_short : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_short record) = 4 /\
      Datatypes.length (bid_price_short record) = 5 /\
      Datatypes.length (bid_quantity_short record) = 5 /\
      Datatypes.length (ask_price_short record) = 5 /\
      Datatypes.length (ask_quantity_short record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (symbol_short record) ++
      encode_bytes 5 (bid_price_short record) ++
      encode_bytes 5 (bid_quantity_short record) ++
      encode_bytes 5 (ask_price_short record) ++
      encode_bytes 5 (ask_quantity_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (symbol_short_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (bid_price_short_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (bid_quantity_short_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (ask_price_short_value, bytes) =>
                      match decode_bytes 5 bytes with
                      | None => None
                      | Some (ask_quantity_short_value, bytes) =>
                          Some ({| symbol_short := symbol_short_value; bid_price_short := bid_price_short_value; bid_quantity_short := bid_quantity_short_value; ask_price_short := ask_price_short_value; ask_quantity_short := ask_quantity_short_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ShortTwoSidedUpdateMessage.

  Module ExpandedTradeMessage.

    (** Expanded Trade Message *)
    Record t := {
      symbol_expanded : list byte;
      last_price_long : list byte;
      last_quantity_long : list byte;
      cumulative_volume_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_expanded record) = 8 /\
      Datatypes.length (last_price_long record) = 10 /\
      Datatypes.length (last_quantity_long record) = 6 /\
      Datatypes.length (cumulative_volume_long record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (symbol_expanded record) ++
      encode_bytes 10 (last_price_long record) ++
      encode_bytes 6 (last_quantity_long record) ++
      encode_bytes 9 (cumulative_volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (symbol_expanded_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (last_price_long_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (last_quantity_long_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (cumulative_volume_long_value, bytes) =>
                      Some ({| symbol_expanded := symbol_expanded_value; last_price_long := last_price_long_value; last_quantity_long := last_quantity_long_value; cumulative_volume_long := cumulative_volume_long_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedTradeMessage.

  Module LongTradeMessage.

    (** Long Trade Message *)
    Record t := {
      symbol_long : list byte;
      last_price_long : list byte;
      last_quantity_long : list byte;
      cumulative_volume_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_long record) = 6 /\
      Datatypes.length (last_price_long record) = 10 /\
      Datatypes.length (last_quantity_long record) = 6 /\
      Datatypes.length (cumulative_volume_long record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (symbol_long record) ++
      encode_bytes 10 (last_price_long record) ++
      encode_bytes 6 (last_quantity_long record) ++
      encode_bytes 9 (cumulative_volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (symbol_long_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (last_price_long_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (last_quantity_long_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (cumulative_volume_long_value, bytes) =>
                      Some ({| symbol_long := symbol_long_value; last_price_long := last_price_long_value; last_quantity_long := last_quantity_long_value; cumulative_volume_long := cumulative_volume_long_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongTradeMessage.

  Module ShortTradeMessage.

    (** Short Trade Message *)
    Record t := {
      symbol_short : list byte;
      last_price_short : list byte;
      last_quantity_short : list byte;
      cumulative_volume_short : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_short record) = 4 /\
      Datatypes.length (last_price_short record) = 5 /\
      Datatypes.length (last_quantity_short record) = 5 /\
      Datatypes.length (cumulative_volume_short record) = 7.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (symbol_short record) ++
      encode_bytes 5 (last_price_short record) ++
      encode_bytes 5 (last_quantity_short record) ++
      encode_bytes 7 (cumulative_volume_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (symbol_short_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (last_price_short_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (last_quantity_short_value, bytes) =>
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (cumulative_volume_short_value, bytes) =>
                      Some ({| symbol_short := symbol_short_value; last_price_short := last_price_short_value; last_quantity_short := last_quantity_short_value; cumulative_volume_short := cumulative_volume_short_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ShortTradeMessage.

  Module TradingStatusMessage.

    (** The Trading Status Message is used to indicate the current trading status of a security. *)
    Record t := {
      symbol_expanded : list byte;
      halt_status : list byte;
      reg_sho_action : list byte;
      reserved_1 : list byte;
      reserved_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_expanded record) = 8 /\
      Datatypes.length (halt_status record) = 1 /\
      Datatypes.length (reg_sho_action record) = 1 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (reserved_2 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (symbol_expanded record) ++
      encode_bytes 1 (halt_status record) ++
      encode_bytes 1 (reg_sho_action record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (symbol_expanded_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (halt_status_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reg_sho_action_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reserved_2_value, bytes) =>
                          Some ({| symbol_expanded := symbol_expanded_value; halt_status := halt_status_value; reg_sho_action := reg_sho_action_value; reserved_1 := reserved_1_value; reserved_2 := reserved_2_value |}, bytes)
                      end
                  end
              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

End ByxEquitiesTopV132.
