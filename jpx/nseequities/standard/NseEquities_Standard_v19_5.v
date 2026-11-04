From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Japan Exchange Group Standard

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

    License: MIT No Attribution
  *)

Module NseEquitiesStandardV195.

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

  Module UpdateNoMessage.

    (** In this tag, Update Number for each issue is set. This tag appears as part of realtime data. *)
    Record t := {
      update_no : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (update_no record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (update_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (update_no_value, bytes) =>
          Some ({| update_no := update_no_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End UpdateNoMessage.

  Module StatusInformation.

    (** Status Information *)
    Record t := {
      issue_status : list byte;
      status_flag : list byte;
      short_selling_regulation_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_status record) = 2 /\
      Datatypes.length (status_flag record) = 2 /\
      Datatypes.length (short_selling_regulation_flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (issue_status record) ++
      encode_bytes 2 (status_flag record) ++
      encode_bytes 1 (short_selling_regulation_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (issue_status_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (status_flag_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (short_selling_regulation_flag_value, bytes) =>
                  Some ({| issue_status := issue_status_value; status_flag := status_flag_value; short_selling_regulation_flag := short_selling_regulation_flag_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End StatusInformation.

  Module StatusInformationMessage.

    (** In this tag, status information (Issue Status, Status Flag and Short Selling Regulation Flag) is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      change_flag : list byte;
      status_information : StatusInformation.t;
      time_c_12 : list byte;
      reserved_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (change_flag record) = 1 /\
      StatusInformation.bounded (status_information record) /\
      Datatypes.length (time_c_12 record) = 12 /\
      Datatypes.length (reserved_4 record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 1 (change_flag record) ++
      StatusInformation.encode (status_information record) ++
      encode_bytes 12 (time_c_12 record) ++
      encode_bytes 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (change_flag_value, bytes) =>
              match StatusInformation.decode bytes with
              | None => None
              | Some (status_information_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (time_c_12_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (reserved_4_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; change_flag := change_flag_value; status_information := status_information_value; time_c_12 := time_c_12_value; reserved_4 := reserved_4_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !StatusInformation.encode_length. reflexivity.
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
      rewrite StatusInformation.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply StatusInformation.eq_dec]. Defined.

  End StatusInformationMessage.

  Module Price.

    (** Price *)
    Record t := {
      unit_flag : list byte;
      price_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (price_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (price_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (price_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; price_c_14 := price_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End Price.

  Module Open.

    (** Open *)
    Record t := {
      price : Price.t;
      time_c_6 : list byte;
      change_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Price.bounded (price record) /\
      Datatypes.length (time_c_6 record) = 6 /\
      Datatypes.length (change_flag record) = 1.

    Definition encode (record : t) : list byte :=
      Price.encode (price record) ++
      encode_bytes 6 (time_c_6 record) ++
      encode_bytes 1 (change_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Price.decode bytes with
      | None => None
      | Some (price_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_c_6_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (change_flag_value, bytes) =>
                  Some ({| price := price_value; time_c_6 := time_c_6_value; change_flag := change_flag_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Price.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Price.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Price.eq_dec]. Defined.

  End Open.

  Module High.

    (** High *)
    Record t := {
      limit_up_flag : list byte;
      price : Price.t;
      time_c_6 : list byte;
      change_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (limit_up_flag record) = 1 /\
      Price.bounded (price record) /\
      Datatypes.length (time_c_6 record) = 6 /\
      Datatypes.length (change_flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (limit_up_flag record) ++
      Price.encode (price record) ++
      encode_bytes 6 (time_c_6 record) ++
      encode_bytes 1 (change_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (limit_up_flag_value, bytes) =>
          match Price.decode bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (time_c_6_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (change_flag_value, bytes) =>
                      Some ({| limit_up_flag := limit_up_flag_value; price := price_value; time_c_6 := time_c_6_value; change_flag := change_flag_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Price.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Price.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Price.eq_dec]. Defined.

  End High.

  Module Low.

    (** Low *)
    Record t := {
      limit_down_flag : list byte;
      price : Price.t;
      time_c_6 : list byte;
      change_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (limit_down_flag record) = 1 /\
      Price.bounded (price record) /\
      Datatypes.length (time_c_6 record) = 6 /\
      Datatypes.length (change_flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (limit_down_flag record) ++
      Price.encode (price record) ++
      encode_bytes 6 (time_c_6 record) ++
      encode_bytes 1 (change_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (limit_down_flag_value, bytes) =>
          match Price.decode bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (time_c_6_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (change_flag_value, bytes) =>
                      Some ({| limit_down_flag := limit_down_flag_value; price := price_value; time_c_6 := time_c_6_value; change_flag := change_flag_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Price.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Price.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Price.eq_dec]. Defined.

  End Low.

  Module Current.

    (** Current *)
    Record t := {
      price : Price.t;
      time_c_12 : list byte;
      current_change_flag : list byte;
      stq_reference_point_flag : list byte;
      reserved_1 : list byte;
      closing_price_input_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Price.bounded (price record) /\
      Datatypes.length (time_c_12 record) = 12 /\
      Datatypes.length (current_change_flag record) = 1 /\
      Datatypes.length (stq_reference_point_flag record) = 1 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (closing_price_input_flag record) = 1.

    Definition encode (record : t) : list byte :=
      Price.encode (price record) ++
      encode_bytes 12 (time_c_12 record) ++
      encode_bytes 1 (current_change_flag record) ++
      encode_bytes 1 (stq_reference_point_flag record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (closing_price_input_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Price.decode bytes with
      | None => None
      | Some (price_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (time_c_12_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (current_change_flag_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (stq_reference_point_flag_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (closing_price_input_flag_value, bytes) =>
                              Some ({| price := price_value; time_c_12 := time_c_12_value; current_change_flag := current_change_flag_value; stq_reference_point_flag := stq_reference_point_flag_value; reserved_1 := reserved_1_value; closing_price_input_flag := closing_price_input_flag_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Price.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Price.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Price.eq_dec]. Defined.

  End Current.

  Module OpenHighLowAndCurrentPriceMessage.

    (** In this tag, Open, High, Low and Current Price and other information are set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      open : Open.t;
      high : High.t;
      low : Low.t;
      current : Current.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Open.bounded (open record) /\
      High.bounded (high record) /\
      Low.bounded (low record) /\
      Current.bounded (current record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      Open.encode (open record) ++
      High.encode (high record) ++
      Low.encode (low record) ++
      Current.encode (current record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match Open.decode bytes with
          | None => None
          | Some (open_value, bytes) =>
              match High.decode bytes with
              | None => None
              | Some (high_value, bytes) =>
                  match Low.decode bytes with
                  | None => None
                  | Some (low_value, bytes) =>
                      match Current.decode bytes with
                      | None => None
                      | Some (current_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; open := open_value; high := high_value; low := low_value; current := current_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 105.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Open.encode_length, !High.encode_length, !Low.encode_length, !Current.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Open.decode_encode by exact bound_1.
      rewrite High.decode_encode by exact bound_2.
      rewrite Low.decode_encode by exact bound_3.
      rewrite Current.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Open.eq_dec | apply High.eq_dec | apply Low.eq_dec | apply Current.eq_dec]. Defined.

  End OpenHighLowAndCurrentPriceMessage.

  Module QuoteQuantity.

    (** Quote Quantity *)
    Record t := {
      trading_volume_turnover_unit_flag : list byte;
      quantity : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (quantity record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (quantity record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (trading_volume_turnover_unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (quantity_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| trading_volume_turnover_unit_flag := trading_volume_turnover_unit_flag_value; quantity := quantity_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End QuoteQuantity.

  Module AskQuote.

    (** Ask Quote *)
    Record t := {
      change_flag : list byte;
      price : Price.t;
      time_c_12 : list byte;
      quote_flag : list byte;
      quote_quantity : QuoteQuantity.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (change_flag record) = 1 /\
      Price.bounded (price record) /\
      Datatypes.length (time_c_12 record) = 12 /\
      Datatypes.length (quote_flag record) = 1 /\
      QuoteQuantity.bounded (quote_quantity record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (change_flag record) ++
      Price.encode (price record) ++
      encode_bytes 12 (time_c_12 record) ++
      encode_bytes 1 (quote_flag record) ++
      QuoteQuantity.encode (quote_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (change_flag_value, bytes) =>
          match Price.decode bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (time_c_12_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (quote_flag_value, bytes) =>
                      match QuoteQuantity.decode bytes with
                      | None => None
                      | Some (quote_quantity_value, bytes) =>
                          Some ({| change_flag := change_flag_value; price := price_value; time_c_12 := time_c_12_value; quote_flag := quote_flag_value; quote_quantity := quote_quantity_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Price.encode_length, !QuoteQuantity.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Price.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite QuoteQuantity.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Price.eq_dec | apply QuoteQuantity.eq_dec]. Defined.

  End AskQuote.

  Module BidQuote.

    (** Bid Quote *)
    Record t := {
      change_flag : list byte;
      price : Price.t;
      time_c_12 : list byte;
      quote_flag : list byte;
      quote_quantity : QuoteQuantity.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (change_flag record) = 1 /\
      Price.bounded (price record) /\
      Datatypes.length (time_c_12 record) = 12 /\
      Datatypes.length (quote_flag record) = 1 /\
      QuoteQuantity.bounded (quote_quantity record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (change_flag record) ++
      Price.encode (price record) ++
      encode_bytes 12 (time_c_12 record) ++
      encode_bytes 1 (quote_flag record) ++
      QuoteQuantity.encode (quote_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (change_flag_value, bytes) =>
          match Price.decode bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (time_c_12_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (quote_flag_value, bytes) =>
                      match QuoteQuantity.decode bytes with
                      | None => None
                      | Some (quote_quantity_value, bytes) =>
                          Some ({| change_flag := change_flag_value; price := price_value; time_c_12 := time_c_12_value; quote_flag := quote_flag_value; quote_quantity := quote_quantity_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Price.encode_length, !QuoteQuantity.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Price.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite QuoteQuantity.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Price.eq_dec | apply QuoteQuantity.eq_dec]. Defined.

  End BidQuote.

  Module Quote1Message.

    (** In this tag, Quote 1 (Ask and Bid Quotes with the Highest Priority) information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      ask_quote : AskQuote.t;
      bid_quote : BidQuote.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      AskQuote.bounded (ask_quote record) /\
      BidQuote.bounded (bid_quote record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      AskQuote.encode (ask_quote record) ++
      BidQuote.encode (bid_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match AskQuote.decode bytes with
          | None => None
          | Some (ask_quote_value, bytes) =>
              match BidQuote.decode bytes with
              | None => None
              | Some (bid_quote_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; ask_quote := ask_quote_value; bid_quote := bid_quote_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !AskQuote.encode_length, !BidQuote.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite AskQuote.decode_encode by exact bound_1.
      rewrite BidQuote.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply AskQuote.eq_dec | apply BidQuote.eq_dec]. Defined.

  End Quote1Message.

  Module Quote2Message.

    (** In this tag, Quote 2 (ask and bid quotes with the 2nd Highest Priority) information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      ask_quote : AskQuote.t;
      bid_quote : BidQuote.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      AskQuote.bounded (ask_quote record) /\
      BidQuote.bounded (bid_quote record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      AskQuote.encode (ask_quote record) ++
      BidQuote.encode (bid_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match AskQuote.decode bytes with
          | None => None
          | Some (ask_quote_value, bytes) =>
              match BidQuote.decode bytes with
              | None => None
              | Some (bid_quote_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; ask_quote := ask_quote_value; bid_quote := bid_quote_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !AskQuote.encode_length, !BidQuote.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite AskQuote.decode_encode by exact bound_1.
      rewrite BidQuote.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply AskQuote.eq_dec | apply BidQuote.eq_dec]. Defined.

  End Quote2Message.

  Module Quote3Message.

    (** In this tag, Quote 3 (ask and bid quotes with the 3rd Highest Priority) information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      ask_quote : AskQuote.t;
      bid_quote : BidQuote.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      AskQuote.bounded (ask_quote record) /\
      BidQuote.bounded (bid_quote record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      AskQuote.encode (ask_quote record) ++
      BidQuote.encode (bid_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match AskQuote.decode bytes with
          | None => None
          | Some (ask_quote_value, bytes) =>
              match BidQuote.decode bytes with
              | None => None
              | Some (bid_quote_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; ask_quote := ask_quote_value; bid_quote := bid_quote_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !AskQuote.encode_length, !BidQuote.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite AskQuote.decode_encode by exact bound_1.
      rewrite BidQuote.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply AskQuote.eq_dec | apply BidQuote.eq_dec]. Defined.

  End Quote3Message.

  Module Quote4Message.

    (** In this tag, Quote 4 (ask and bid quotes with the 4th Highest Priority) information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      ask_quote : AskQuote.t;
      bid_quote : BidQuote.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      AskQuote.bounded (ask_quote record) /\
      BidQuote.bounded (bid_quote record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      AskQuote.encode (ask_quote record) ++
      BidQuote.encode (bid_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match AskQuote.decode bytes with
          | None => None
          | Some (ask_quote_value, bytes) =>
              match BidQuote.decode bytes with
              | None => None
              | Some (bid_quote_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; ask_quote := ask_quote_value; bid_quote := bid_quote_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !AskQuote.encode_length, !BidQuote.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite AskQuote.decode_encode by exact bound_1.
      rewrite BidQuote.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply AskQuote.eq_dec | apply BidQuote.eq_dec]. Defined.

  End Quote4Message.

  Module Quote5Message.

    (** In this tag, Quote 5 (ask and bid quotes with the 5th Highest Priority) information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      ask_quote : AskQuote.t;
      bid_quote : BidQuote.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      AskQuote.bounded (ask_quote record) /\
      BidQuote.bounded (bid_quote record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      AskQuote.encode (ask_quote record) ++
      BidQuote.encode (bid_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match AskQuote.decode bytes with
          | None => None
          | Some (ask_quote_value, bytes) =>
              match BidQuote.decode bytes with
              | None => None
              | Some (bid_quote_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; ask_quote := ask_quote_value; bid_quote := bid_quote_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !AskQuote.encode_length, !BidQuote.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite AskQuote.decode_encode by exact bound_1.
      rewrite BidQuote.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply AskQuote.eq_dec | apply BidQuote.eq_dec]. Defined.

  End Quote5Message.

  Module Quote6Message.

    (** In this tag, Quote 6 (ask and bid quotes with the 6th Highest Priority) information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      ask_quote : AskQuote.t;
      bid_quote : BidQuote.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      AskQuote.bounded (ask_quote record) /\
      BidQuote.bounded (bid_quote record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      AskQuote.encode (ask_quote record) ++
      BidQuote.encode (bid_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match AskQuote.decode bytes with
          | None => None
          | Some (ask_quote_value, bytes) =>
              match BidQuote.decode bytes with
              | None => None
              | Some (bid_quote_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; ask_quote := ask_quote_value; bid_quote := bid_quote_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !AskQuote.encode_length, !BidQuote.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite AskQuote.decode_encode by exact bound_1.
      rewrite BidQuote.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply AskQuote.eq_dec | apply BidQuote.eq_dec]. Defined.

  End Quote6Message.

  Module Quote7Message.

    (** In this tag, Quote 7 (ask and bid quotes with the 7th Highest Priority) information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      ask_quote : AskQuote.t;
      bid_quote : BidQuote.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      AskQuote.bounded (ask_quote record) /\
      BidQuote.bounded (bid_quote record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      AskQuote.encode (ask_quote record) ++
      BidQuote.encode (bid_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match AskQuote.decode bytes with
          | None => None
          | Some (ask_quote_value, bytes) =>
              match BidQuote.decode bytes with
              | None => None
              | Some (bid_quote_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; ask_quote := ask_quote_value; bid_quote := bid_quote_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !AskQuote.encode_length, !BidQuote.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite AskQuote.decode_encode by exact bound_1.
      rewrite BidQuote.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply AskQuote.eq_dec | apply BidQuote.eq_dec]. Defined.

  End Quote7Message.

  Module Quote8Message.

    (** In this tag, Quote 8 (ask and bid quotes with the 8th Highest Priority) information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      ask_quote : AskQuote.t;
      bid_quote : BidQuote.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      AskQuote.bounded (ask_quote record) /\
      BidQuote.bounded (bid_quote record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      AskQuote.encode (ask_quote record) ++
      BidQuote.encode (bid_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match AskQuote.decode bytes with
          | None => None
          | Some (ask_quote_value, bytes) =>
              match BidQuote.decode bytes with
              | None => None
              | Some (bid_quote_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; ask_quote := ask_quote_value; bid_quote := bid_quote_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !AskQuote.encode_length, !BidQuote.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite AskQuote.decode_encode by exact bound_1.
      rewrite BidQuote.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply AskQuote.eq_dec | apply BidQuote.eq_dec]. Defined.

  End Quote8Message.

  Module Quote9Message.

    (** In this tag, Quote 9 (ask and bid quotes with the 9th Highest Priority) information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      ask_quote : AskQuote.t;
      bid_quote : BidQuote.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      AskQuote.bounded (ask_quote record) /\
      BidQuote.bounded (bid_quote record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      AskQuote.encode (ask_quote record) ++
      BidQuote.encode (bid_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match AskQuote.decode bytes with
          | None => None
          | Some (ask_quote_value, bytes) =>
              match BidQuote.decode bytes with
              | None => None
              | Some (bid_quote_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; ask_quote := ask_quote_value; bid_quote := bid_quote_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !AskQuote.encode_length, !BidQuote.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite AskQuote.decode_encode by exact bound_1.
      rewrite BidQuote.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply AskQuote.eq_dec | apply BidQuote.eq_dec]. Defined.

  End Quote9Message.

  Module Quote10Message.

    (** In this tag, Quote 10 (ask and bid quotes with the 10th Highest Priority) information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      ask_quote : AskQuote.t;
      bid_quote : BidQuote.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      AskQuote.bounded (ask_quote record) /\
      BidQuote.bounded (bid_quote record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      AskQuote.encode (ask_quote record) ++
      BidQuote.encode (bid_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match AskQuote.decode bytes with
          | None => None
          | Some (ask_quote_value, bytes) =>
              match BidQuote.decode bytes with
              | None => None
              | Some (bid_quote_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; ask_quote := ask_quote_value; bid_quote := bid_quote_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !AskQuote.encode_length, !BidQuote.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite AskQuote.decode_encode by exact bound_1.
      rewrite BidQuote.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply AskQuote.eq_dec | apply BidQuote.eq_dec]. Defined.

  End Quote10Message.

  Module SellOrder.

    (** Sell Order *)
    Record t := {
      change_flag : list byte;
      time_c_12 : list byte;
      quote_quantity : QuoteQuantity.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (change_flag record) = 1 /\
      Datatypes.length (time_c_12 record) = 12 /\
      QuoteQuantity.bounded (quote_quantity record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (change_flag record) ++
      encode_bytes 12 (time_c_12 record) ++
      QuoteQuantity.encode (quote_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (change_flag_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (time_c_12_value, bytes) =>
              match QuoteQuantity.decode bytes with
              | None => None
              | Some (quote_quantity_value, bytes) =>
                  Some ({| change_flag := change_flag_value; time_c_12 := time_c_12_value; quote_quantity := quote_quantity_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !QuoteQuantity.encode_length. reflexivity.
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
      rewrite QuoteQuantity.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply QuoteQuantity.eq_dec]. Defined.

  End SellOrder.

  Module BuyOrder.

    (** Buy Order *)
    Record t := {
      change_flag : list byte;
      time_c_12 : list byte;
      quote_quantity : QuoteQuantity.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (change_flag record) = 1 /\
      Datatypes.length (time_c_12 record) = 12 /\
      QuoteQuantity.bounded (quote_quantity record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (change_flag record) ++
      encode_bytes 12 (time_c_12 record) ++
      QuoteQuantity.encode (quote_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (change_flag_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (time_c_12_value, bytes) =>
              match QuoteQuantity.decode bytes with
              | None => None
              | Some (quote_quantity_value, bytes) =>
                  Some ({| change_flag := change_flag_value; time_c_12 := time_c_12_value; quote_quantity := quote_quantity_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !QuoteQuantity.encode_length. reflexivity.
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
      rewrite QuoteQuantity.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply QuoteQuantity.eq_dec]. Defined.

  End BuyOrder.

  Module MarketOrderMessage.

    (** In this tag, both Ask and Bid Market Order Information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      sell_order : SellOrder.t;
      buy_order : BuyOrder.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      SellOrder.bounded (sell_order record) /\
      BuyOrder.bounded (buy_order record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      SellOrder.encode (sell_order record) ++
      BuyOrder.encode (buy_order record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match SellOrder.decode bytes with
          | None => None
          | Some (sell_order_value, bytes) =>
              match BuyOrder.decode bytes with
              | None => None
              | Some (buy_order_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; sell_order := sell_order_value; buy_order := buy_order_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !SellOrder.encode_length, !BuyOrder.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite SellOrder.decode_encode by exact bound_1.
      rewrite BuyOrder.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SellOrder.eq_dec | apply BuyOrder.eq_dec]. Defined.

  End MarketOrderMessage.

  Module OverQuote.

    (** OVER Quote *)
    Record t := {
      change_flag : list byte;
      time_c_12 : list byte;
      quote_quantity : QuoteQuantity.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (change_flag record) = 1 /\
      Datatypes.length (time_c_12 record) = 12 /\
      QuoteQuantity.bounded (quote_quantity record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (change_flag record) ++
      encode_bytes 12 (time_c_12 record) ++
      QuoteQuantity.encode (quote_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (change_flag_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (time_c_12_value, bytes) =>
              match QuoteQuantity.decode bytes with
              | None => None
              | Some (quote_quantity_value, bytes) =>
                  Some ({| change_flag := change_flag_value; time_c_12 := time_c_12_value; quote_quantity := quote_quantity_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !QuoteQuantity.encode_length. reflexivity.
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
      rewrite QuoteQuantity.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply QuoteQuantity.eq_dec]. Defined.

  End OverQuote.

  Module UnderQuote.

    (** UNDER Quote *)
    Record t := {
      change_flag : list byte;
      time_c_12 : list byte;
      quote_quantity : QuoteQuantity.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (change_flag record) = 1 /\
      Datatypes.length (time_c_12 record) = 12 /\
      QuoteQuantity.bounded (quote_quantity record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (change_flag record) ++
      encode_bytes 12 (time_c_12 record) ++
      QuoteQuantity.encode (quote_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (change_flag_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (time_c_12_value, bytes) =>
              match QuoteQuantity.decode bytes with
              | None => None
              | Some (quote_quantity_value, bytes) =>
                  Some ({| change_flag := change_flag_value; time_c_12 := time_c_12_value; quote_quantity := quote_quantity_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !QuoteQuantity.encode_length. reflexivity.
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
      rewrite QuoteQuantity.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply QuoteQuantity.eq_dec]. Defined.

  End UnderQuote.

  Module OverUnderMessage.

    (** In this tag, OVER/UNDER quote (Total of quote 11 (Ask) and above or quote 11 (Bid) and below) information is set. This tag is appeared as one of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      over_quote : OverQuote.t;
      under_quote : UnderQuote.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      OverQuote.bounded (over_quote record) /\
      UnderQuote.bounded (under_quote record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      OverQuote.encode (over_quote record) ++
      UnderQuote.encode (under_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match OverQuote.decode bytes with
          | None => None
          | Some (over_quote_value, bytes) =>
              match UnderQuote.decode bytes with
              | None => None
              | Some (under_quote_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; over_quote := over_quote_value; under_quote := under_quote_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !OverQuote.encode_length, !UnderQuote.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite OverQuote.decode_encode by exact bound_1.
      rewrite UnderQuote.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OverQuote.eq_dec | apply UnderQuote.eq_dec]. Defined.

  End OverUnderMessage.

  Module TradingVolume.

    (** Trading Volume *)
    Record t := {
      reserved_1 : list byte;
      trading_volume_turnover_unit_flag : list byte;
      trading_volume_c_14 : list byte;
      time_c_6 : list byte;
      second_reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (trading_volume_c_14 record) = 14 /\
      Datatypes.length (time_c_6 record) = 6 /\
      Datatypes.length (second_reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (trading_volume_c_14 record) ++
      encode_bytes 6 (time_c_6 record) ++
      encode_bytes 1 (second_reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reserved_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_volume_turnover_unit_flag_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (trading_volume_c_14_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_c_6_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (second_reserved_1_value, bytes) =>
                          Some ({| reserved_1 := reserved_1_value; trading_volume_turnover_unit_flag := trading_volume_turnover_unit_flag_value; trading_volume_c_14 := trading_volume_c_14_value; time_c_6 := time_c_6_value; second_reserved_1 := second_reserved_1_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End TradingVolume.

  Module TradingVolumeMessage.

    (** In this tag, by-issue trading volume information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      trading_volume : TradingVolume.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      TradingVolume.bounded (trading_volume record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      TradingVolume.encode (trading_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match TradingVolume.decode bytes with
          | None => None
          | Some (trading_volume_value, bytes) =>
              Some ({| reserved_2 := reserved_2_value; trading_volume := trading_volume_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !TradingVolume.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite TradingVolume.decode_encode by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TradingVolume.eq_dec]. Defined.

  End TradingVolumeMessage.

  Module TurnoverInYenValue.

    (** Turnover in yen value *)
    Record t := {
      reserved_1 : list byte;
      trading_volume_turnover_unit_flag : list byte;
      turnover_value : list byte;
      time_c_6 : list byte;
      second_reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (turnover_value record) = 14 /\
      Datatypes.length (time_c_6 record) = 6 /\
      Datatypes.length (second_reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (turnover_value record) ++
      encode_bytes 6 (time_c_6 record) ++
      encode_bytes 1 (second_reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reserved_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_volume_turnover_unit_flag_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (turnover_value_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_c_6_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (second_reserved_1_value, bytes) =>
                          Some ({| reserved_1 := reserved_1_value; trading_volume_turnover_unit_flag := trading_volume_turnover_unit_flag_value; turnover_value := turnover_value_value; time_c_6 := time_c_6_value; second_reserved_1 := second_reserved_1_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End TurnoverInYenValue.

  Module TurnoverMessage.

    (** In this tag, by-issue Turnover Information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      turnover_in_yen_value : TurnoverInYenValue.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      TurnoverInYenValue.bounded (turnover_in_yen_value record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      TurnoverInYenValue.encode (turnover_in_yen_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match TurnoverInYenValue.decode bytes with
          | None => None
          | Some (turnover_in_yen_value_value, bytes) =>
              Some ({| reserved_2 := reserved_2_value; turnover_in_yen_value := turnover_in_yen_value_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !TurnoverInYenValue.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite TurnoverInYenValue.decode_encode by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TurnoverInYenValue.eq_dec]. Defined.

  End TurnoverMessage.

  Module AllDayVwap.

    (** All-Day VWAP *)
    Record t := {
      reserved_1 : list byte;
      lot_size_unit_flag : list byte;
      all_day_vwap_c_14 : list byte;
      sign : list byte;
      time_c_6 : list byte;
      second_reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (lot_size_unit_flag record) = 1 /\
      Datatypes.length (all_day_vwap_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (time_c_6 record) = 6 /\
      Datatypes.length (second_reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (lot_size_unit_flag record) ++
      encode_bytes 14 (all_day_vwap_c_14 record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 6 (time_c_6 record) ++
      encode_bytes 1 (second_reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reserved_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (lot_size_unit_flag_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (all_day_vwap_c_14_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sign_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (time_c_6_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_reserved_1_value, bytes) =>
                              Some ({| reserved_1 := reserved_1_value; lot_size_unit_flag := lot_size_unit_flag_value; all_day_vwap_c_14 := all_day_vwap_c_14_value; sign := sign_value; time_c_6 := time_c_6_value; second_reserved_1 := second_reserved_1_value |}, bytes)
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AllDayVwap.

  Module CurrentSessionVwap.

    (** Current-Session VWAP *)
    Record t := {
      reserved_1 : list byte;
      lot_size_unit_flag : list byte;
      current_session_vwap_c_14 : list byte;
      sign : list byte;
      time_c_6 : list byte;
      second_reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (lot_size_unit_flag record) = 1 /\
      Datatypes.length (current_session_vwap_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (time_c_6 record) = 6 /\
      Datatypes.length (second_reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (lot_size_unit_flag record) ++
      encode_bytes 14 (current_session_vwap_c_14 record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 6 (time_c_6 record) ++
      encode_bytes 1 (second_reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reserved_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (lot_size_unit_flag_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (current_session_vwap_c_14_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sign_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (time_c_6_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_reserved_1_value, bytes) =>
                              Some ({| reserved_1 := reserved_1_value; lot_size_unit_flag := lot_size_unit_flag_value; current_session_vwap_c_14 := current_session_vwap_c_14_value; sign := sign_value; time_c_6 := time_c_6_value; second_reserved_1 := second_reserved_1_value |}, bytes)
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CurrentSessionVwap.

  Module VwapMessage.

    (** In this tag, by-issue Volume Weighted Stock Price average (VWAP) Information is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      all_day_vwap : AllDayVwap.t;
      current_session_vwap : CurrentSessionVwap.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      AllDayVwap.bounded (all_day_vwap record) /\
      CurrentSessionVwap.bounded (current_session_vwap record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      AllDayVwap.encode (all_day_vwap record) ++
      CurrentSessionVwap.encode (current_session_vwap record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match AllDayVwap.decode bytes with
          | None => None
          | Some (all_day_vwap_value, bytes) =>
              match CurrentSessionVwap.decode bytes with
              | None => None
              | Some (current_session_vwap_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; all_day_vwap := all_day_vwap_value; current_session_vwap := current_session_vwap_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !AllDayVwap.encode_length, !CurrentSessionVwap.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite AllDayVwap.decode_encode by exact bound_1.
      rewrite CurrentSessionVwap.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply AllDayVwap.eq_dec | apply CurrentSessionVwap.eq_dec]. Defined.

  End VwapMessage.

  Module ParityEstimatedPrice.

    (** Parity/Estimated Price *)
    Record t := {
      unit_flag : list byte;
      parity_estimated_price_c_14 : list byte;
      sign : list byte;
      time_c_6 : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (parity_estimated_price_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (time_c_6 record) = 6 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (parity_estimated_price_c_14 record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 6 (time_c_6 record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (parity_estimated_price_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_c_6_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          Some ({| unit_flag := unit_flag_value; parity_estimated_price_c_14 := parity_estimated_price_c_14_value; sign := sign_value; time_c_6 := time_c_6_value; reserved_1 := reserved_1_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End ParityEstimatedPrice.

  Module ParityMessage.

    (** In this tag, estimated Price Information for parity of CB is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      parity_estimated_price : ParityEstimatedPrice.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      ParityEstimatedPrice.bounded (parity_estimated_price record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      ParityEstimatedPrice.encode (parity_estimated_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match ParityEstimatedPrice.decode bytes with
          | None => None
          | Some (parity_estimated_price_value, bytes) =>
              Some ({| reserved_2 := reserved_2_value; parity_estimated_price := parity_estimated_price_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParityEstimatedPrice.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParityEstimatedPrice.decode_encode by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParityEstimatedPrice.eq_dec]. Defined.

  End ParityMessage.

  Module DirectYield.

    (** Direct Yield *)
    Record t := {
      direct_yield_c_8 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (direct_yield_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (direct_yield_c_8 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (direct_yield_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              Some ({| direct_yield_c_8 := direct_yield_c_8_value; sign := sign_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End DirectYield.

  Module FinalYield.

    (** Final Yield *)
    Record t := {
      final_yield_c_8 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (final_yield_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (final_yield_c_8 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (final_yield_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              Some ({| final_yield_c_8 := final_yield_c_8_value; sign := sign_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End FinalYield.

  Module YieldMessage.

    (** In this tag, Direct and Final Yield Information for CB is set. This tag appears as part of realtime data. *)
    Record t := {
      reserved_2 : list byte;
      direct_yield : DirectYield.t;
      final_yield : FinalYield.t;
      time_c_6 : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      DirectYield.bounded (direct_yield record) /\
      FinalYield.bounded (final_yield record) /\
      Datatypes.length (time_c_6 record) = 6 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      DirectYield.encode (direct_yield record) ++
      FinalYield.encode (final_yield record) ++
      encode_bytes 6 (time_c_6 record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match DirectYield.decode bytes with
          | None => None
          | Some (direct_yield_value, bytes) =>
              match FinalYield.decode bytes with
              | None => None
              | Some (final_yield_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_c_6_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; direct_yield := direct_yield_value; final_yield := final_yield_value; time_c_6 := time_c_6_value; reserved_1 := reserved_1_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !DirectYield.encode_length, !FinalYield.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite DirectYield.decode_encode by exact bound_1.
      rewrite FinalYield.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply DirectYield.eq_dec | apply FinalYield.eq_dec]. Defined.

  End YieldMessage.

  Module ControlMessage.

    (** In this tag, the Test Mode Flag and the Start/End Flag that are used in a Control Message are set. This tag appears as part of a Control Message. *)
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

End NseEquitiesStandardV195.
