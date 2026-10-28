From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Japan Exchange Group ToSTNeT

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

Module TseEquitiesToSTNeTV195.

  Module MessageSerialNo.

    (** Numbered from 1 on each Multicast Group, with the multicast group number in the first to third byte *)
    Record t := {
      multicast_group_number : list byte;
      sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (multicast_group_number record) = 3 /\
      Datatypes.length (sequence_number record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (multicast_group_number record) ++
      encode_bytes 8 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (multicast_group_number_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              Some ({| multicast_group_number := multicast_group_number_value; sequence_number := sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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

  End MessageSerialNo.

  Module IssueClassification.

    (** Set in issue realtime message and issue basic message. In the case of Control, Index and Statistics Message, space is set. *)
    Record t := {
      issue_classification_large_classification : list byte;
      issue_classification_medium_classification : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_classification_large_classification record) = 2 /\
      Datatypes.length (issue_classification_medium_classification record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (issue_classification_large_classification record) ++
      encode_bytes 2 (issue_classification_medium_classification record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (issue_classification_large_classification_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (issue_classification_medium_classification_value, bytes) =>
              Some ({| issue_classification_large_classification := issue_classification_large_classification_value; issue_classification_medium_classification := issue_classification_medium_classification_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End IssueClassification.

  Module StockIssueCode.

    (** Issue Code layout a. Stocks, used when Issue Classification Large Classification is 01 Stock-Related. FLEX Issue Code is set with right-align. *)
    Record t := {
      stock_space : list byte;
      stock_proper_name_code : list byte;
      stock_reserved_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_space record) = 7 /\
      Datatypes.length (stock_proper_name_code record) = 4 /\
      Datatypes.length (stock_reserved_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (stock_space record) ++
      encode_bytes 4 (stock_proper_name_code record) ++
      encode_bytes 1 (stock_reserved_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (stock_space_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (stock_proper_name_code_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (stock_reserved_code_value, bytes) =>
                  Some ({| stock_space := stock_space_value; stock_proper_name_code := stock_proper_name_code_value; stock_reserved_code := stock_reserved_code_value |}, bytes)
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

  End StockIssueCode.

  Module CBIssueCode.

    (** Issue Code layout used when Issue Classification Large Classification is 02 CB-Related. The figure carries no label of its own in 5.3.3 (7). FLEX Issue Code is set with right-align. *)
    Record t := {
      c_b_space : list byte;
      c_b_reserved_code : list byte;
      time_symbol : list byte;
      c_b_proper_name_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (c_b_space record) = 3 /\
      Datatypes.length (c_b_reserved_code record) = 1 /\
      Datatypes.length (time_symbol record) = 4 /\
      Datatypes.length (c_b_proper_name_code record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (c_b_space record) ++
      encode_bytes 1 (c_b_reserved_code record) ++
      encode_bytes 4 (time_symbol record) ++
      encode_bytes 4 (c_b_proper_name_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (c_b_space_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (c_b_reserved_code_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (time_symbol_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (c_b_proper_name_code_value, bytes) =>
                      Some ({| c_b_space := c_b_space_value; c_b_reserved_code := c_b_reserved_code_value; time_symbol := time_symbol_value; c_b_proper_name_code := c_b_proper_name_code_value |}, bytes)
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

  End CBIssueCode.

  Module TradingHalt.

    (** Trading Halt *)
    Record t := {
      state_flag : list byte;
      time_c_6 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (state_flag record) = 2 /\
      Datatypes.length (time_c_6 record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (state_flag record) ++
      encode_bytes 6 (time_c_6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (state_flag_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_c_6_value, bytes) =>
              Some ({| state_flag := state_flag_value; time_c_6 := time_c_6_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End TradingHalt.

  Module Price.

    (** Price *)
    Record t := {
      price_code : list byte;
      lot_size_unit_flag : list byte;
      price_c_14 : list byte;
      sign : list byte;
      time_c_12 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (price_code record) = 2 /\
      Datatypes.length (lot_size_unit_flag record) = 1 /\
      Datatypes.length (price_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (time_c_12 record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (price_code record) ++
      encode_bytes 1 (lot_size_unit_flag record) ++
      encode_bytes 14 (price_c_14 record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 12 (time_c_12 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (price_code_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (lot_size_unit_flag_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (price_c_14_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sign_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (time_c_12_value, bytes) =>
                          Some ({| price_code := price_code_value; lot_size_unit_flag := lot_size_unit_flag_value; price_c_14 := price_c_14_value; sign := sign_value; time_c_12 := time_c_12_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End Price.

  Module TradingVolume.

    (** Trading Volume *)
    Record t := {
      trading_volume_turnover_unit_flag : list byte;
      trading_volume_c_14 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (trading_volume_c_14 record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (trading_volume_c_14 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (trading_volume_turnover_unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (trading_volume_c_14_value, bytes) =>
              Some ({| trading_volume_turnover_unit_flag := trading_volume_turnover_unit_flag_value; trading_volume_c_14 := trading_volume_c_14_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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

  End TradingVolume.

  Module Turnover.

    (** Turnover *)
    Record t := {
      trading_volume_turnover_unit_flag : list byte;
      turnover_c_14 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (turnover_c_14 record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (turnover_c_14 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (trading_volume_turnover_unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (turnover_c_14_value, bytes) =>
              Some ({| trading_volume_turnover_unit_flag := trading_volume_turnover_unit_flag_value; turnover_c_14 := turnover_c_14_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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

  End Turnover.

  Module ToSTNeTBy_IssueInformationMessage.

    (** In this tag, information concerning trade and trading halt for an issue (single-issue transaction, basket transaction, or closing price transaction) on the ToSTNeT is set. This data appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      market_identification_flag : list byte;
      trading_halt : TradingHalt.t;
      transaction_identification_flag : list byte;
      price : Price.t;
      trading_volume : TradingVolume.t;
      turnover : Turnover.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (market_identification_flag record) = 1 /\
      TradingHalt.bounded (trading_halt record) /\
      Datatypes.length (transaction_identification_flag record) = 1 /\
      Price.bounded (price record) /\
      TradingVolume.bounded (trading_volume record) /\
      Turnover.bounded (turnover record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 1 (market_identification_flag record) ++
      TradingHalt.encode (trading_halt record) ++
      encode_bytes 1 (transaction_identification_flag record) ++
      Price.encode (price record) ++
      TradingVolume.encode (trading_volume record) ++
      Turnover.encode (turnover record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_identification_flag_value, bytes) =>
              match TradingHalt.decode bytes with
              | None => None
              | Some (trading_halt_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (transaction_identification_flag_value, bytes) =>
                      match Price.decode bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match TradingVolume.decode bytes with
                          | None => None
                          | Some (trading_volume_value, bytes) =>
                              match Turnover.decode bytes with
                              | None => None
                              | Some (turnover_value, bytes) =>
                                  Some ({| reserved_2 := reserved_2_value; market_identification_flag := market_identification_flag_value; trading_halt := trading_halt_value; transaction_identification_flag := transaction_identification_flag_value; price := price_value; trading_volume := trading_volume_value; turnover := turnover_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !TradingHalt.encode_length, !Price.encode_length, !TradingVolume.encode_length, !Turnover.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite TradingHalt.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite Price.decode_encode by exact bound_4.
      rewrite TradingVolume.decode_encode by exact bound_5.
      rewrite Turnover.decode_encode by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TradingHalt.eq_dec | apply Price.eq_dec | apply TradingVolume.eq_dec | apply Turnover.eq_dec]. Defined.

  End ToSTNeTBy_IssueInformationMessage.

  Module State.

    (** State *)
    Record t := {
      market_state_flag : list byte;
      time_c_6 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_state_flag record) = 2 /\
      Datatypes.length (time_c_6 record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (market_state_flag record) ++
      encode_bytes 6 (time_c_6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (market_state_flag_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_c_6_value, bytes) =>
              Some ({| market_state_flag := market_state_flag_value; time_c_6 := time_c_6_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End State.

  Module ToSTNeTMarketInformationMessage.

    (** In this tag, state information on the ToSTNeT will be set. This data appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      market_identification_flag : list byte;
      state : State.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (market_identification_flag record) = 1 /\
      State.bounded (state record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 1 (market_identification_flag record) ++
      State.encode (state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_identification_flag_value, bytes) =>
              match State.decode bytes with
              | None => None
              | Some (state_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; market_identification_flag := market_identification_flag_value; state := state_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !State.encode_length. reflexivity.
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
      rewrite State.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply State.eq_dec]. Defined.

  End ToSTNeTMarketInformationMessage.

  Module ControlMessage.

    (** In this tag, the test mode flag and the start/end flag that are used in a control message will be set. This tag will be edited into a control message (communication control and health check control) for output. *)
    Record t := {
      reserved_2 : list byte;
      test_mode_flag : list byte;
      start_end_flag : list byte;
      time_c_6 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (test_mode_flag record) = 1 /\
      Datatypes.length (start_end_flag record) = 1 /\
      Datatypes.length (time_c_6 record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 1 (test_mode_flag record) ++
      encode_bytes 1 (start_end_flag record) ++
      encode_bytes 6 (time_c_6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (test_mode_flag_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (start_end_flag_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_c_6_value, bytes) =>
                      Some ({| reserved_2 := reserved_2_value; test_mode_flag := test_mode_flag_value; start_end_flag := start_end_flag_value; time_c_6 := time_c_6_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End ControlMessage.

End TseEquitiesToSTNeTV195.
