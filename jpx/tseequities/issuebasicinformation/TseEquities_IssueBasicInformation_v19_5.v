From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Japan Exchange Group IssueBasicInformation

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

Module TseEquitiesIssueBasicInformationV195.

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

  Module IndexConstituentIssue.

    (** Index constituent issue *)
    Record t := {
      arbitrary_1 : list byte;
      arbitrary_2 : list byte;
      arbitrary_3 : list byte;
      arbitrary_4 : list byte;
      arbitrary_5 : list byte;
      arbitrary_6 : list byte;
      arbitrary_7 : list byte;
      arbitrary_8_to_10 : list byte;
      arbitrary_11 : list byte;
      arbitrary_12_to_15 : list byte;
      arbitrary_16 : list byte;
      arbitrary_17_to_19 : list byte;
      arbitrary_20 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (arbitrary_1 record) = 1 /\
      Datatypes.length (arbitrary_2 record) = 1 /\
      Datatypes.length (arbitrary_3 record) = 1 /\
      Datatypes.length (arbitrary_4 record) = 1 /\
      Datatypes.length (arbitrary_5 record) = 1 /\
      Datatypes.length (arbitrary_6 record) = 1 /\
      Datatypes.length (arbitrary_7 record) = 1 /\
      Datatypes.length (arbitrary_8_to_10 record) = 3 /\
      Datatypes.length (arbitrary_11 record) = 1 /\
      Datatypes.length (arbitrary_12_to_15 record) = 4 /\
      Datatypes.length (arbitrary_16 record) = 1 /\
      Datatypes.length (arbitrary_17_to_19 record) = 3 /\
      Datatypes.length (arbitrary_20 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (arbitrary_1 record) ++
      encode_bytes 1 (arbitrary_2 record) ++
      encode_bytes 1 (arbitrary_3 record) ++
      encode_bytes 1 (arbitrary_4 record) ++
      encode_bytes 1 (arbitrary_5 record) ++
      encode_bytes 1 (arbitrary_6 record) ++
      encode_bytes 1 (arbitrary_7 record) ++
      encode_bytes 3 (arbitrary_8_to_10 record) ++
      encode_bytes 1 (arbitrary_11 record) ++
      encode_bytes 4 (arbitrary_12_to_15 record) ++
      encode_bytes 1 (arbitrary_16 record) ++
      encode_bytes 3 (arbitrary_17_to_19 record) ++
      encode_bytes 1 (arbitrary_20 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (arbitrary_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (arbitrary_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (arbitrary_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (arbitrary_4_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (arbitrary_5_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (arbitrary_6_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (arbitrary_7_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (arbitrary_8_to_10_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (arbitrary_11_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (arbitrary_12_to_15_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (arbitrary_16_value, bytes) =>
                                                  match decode_bytes 3 bytes with
                                                  | None => None
                                                  | Some (arbitrary_17_to_19_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (arbitrary_20_value, bytes) =>
                                                          Some ({| arbitrary_1 := arbitrary_1_value; arbitrary_2 := arbitrary_2_value; arbitrary_3 := arbitrary_3_value; arbitrary_4 := arbitrary_4_value; arbitrary_5 := arbitrary_5_value; arbitrary_6 := arbitrary_6_value; arbitrary_7 := arbitrary_7_value; arbitrary_8_to_10 := arbitrary_8_to_10_value; arbitrary_11 := arbitrary_11_value; arbitrary_12_to_15 := arbitrary_12_to_15_value; arbitrary_16 := arbitrary_16_value; arbitrary_17_to_19 := arbitrary_17_to_19_value; arbitrary_20 := arbitrary_20_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexConstituentIssue.

  Module NewOrdersProhibition.

    (** New Orders Prohibition *)
    Record t := {
      market_limit_orders : list byte;
      side : list byte;
      proprietary_brokerage : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_limit_orders record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (proprietary_brokerage record) = 1 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_limit_orders record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (proprietary_brokerage record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_limit_orders_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (proprietary_brokerage_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      Some ({| market_limit_orders := market_limit_orders_value; side := side_value; proprietary_brokerage := proprietary_brokerage_value; reserved_1 := reserved_1_value |}, bytes)
                  end
              end
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

  End NewOrdersProhibition.

  Module MarginTransactionsProhibition.

    (** Margin Transactions Prohibition *)
    Record t := {
      side : list byte;
      proprietary_brokerage : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (side record) = 1 /\
      Datatypes.length (proprietary_brokerage record) = 1 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (side record) ++
      encode_bytes 1 (proprietary_brokerage record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (side_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (proprietary_brokerage_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  Some ({| side := side_value; proprietary_brokerage := proprietary_brokerage_value; reserved_1 := reserved_1_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End MarginTransactionsProhibition.

  Module ShortSellingProhibition.

    (** Short Selling Prohibition *)
    Record t := {
      proprietary_brokerage : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (proprietary_brokerage record) = 1 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (proprietary_brokerage record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (proprietary_brokerage_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reserved_1_value, bytes) =>
              Some ({| proprietary_brokerage := proprietary_brokerage_value; reserved_1 := reserved_1_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End ShortSellingProhibition.

  Module OrderProhibitionStatusAtTheRegularDistribution.

    (** Order Prohibition Status (at the regular distribution) *)
    Record t := {
      new_orders_prohibition : NewOrdersProhibition.t;
      margin_transactions_prohibition : MarginTransactionsProhibition.t;
      short_selling_prohibition : ShortSellingProhibition.t;
      all_orders_prohibition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      NewOrdersProhibition.bounded (new_orders_prohibition record) /\
      MarginTransactionsProhibition.bounded (margin_transactions_prohibition record) /\
      ShortSellingProhibition.bounded (short_selling_prohibition record) /\
      Datatypes.length (all_orders_prohibition record) = 1.

    Definition encode (record : t) : list byte :=
      NewOrdersProhibition.encode (new_orders_prohibition record) ++
      MarginTransactionsProhibition.encode (margin_transactions_prohibition record) ++
      ShortSellingProhibition.encode (short_selling_prohibition record) ++
      encode_bytes 1 (all_orders_prohibition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match NewOrdersProhibition.decode bytes with
      | None => None
      | Some (new_orders_prohibition_value, bytes) =>
          match MarginTransactionsProhibition.decode bytes with
          | None => None
          | Some (margin_transactions_prohibition_value, bytes) =>
              match ShortSellingProhibition.decode bytes with
              | None => None
              | Some (short_selling_prohibition_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (all_orders_prohibition_value, bytes) =>
                      Some ({| new_orders_prohibition := new_orders_prohibition_value; margin_transactions_prohibition := margin_transactions_prohibition_value; short_selling_prohibition := short_selling_prohibition_value; all_orders_prohibition := all_orders_prohibition_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !NewOrdersProhibition.encode_length, !MarginTransactionsProhibition.encode_length, !ShortSellingProhibition.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite NewOrdersProhibition.decode_encode by exact bound_0.
      rewrite MarginTransactionsProhibition.decode_encode by exact bound_1.
      rewrite ShortSellingProhibition.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply NewOrdersProhibition.eq_dec | apply MarginTransactionsProhibition.eq_dec | apply ShortSellingProhibition.eq_dec]. Defined.

  End OrderProhibitionStatusAtTheRegularDistribution.

  Module IssueInformationMessage.

    (** In this tag, the new security code, etc., of each issue will be set. This tag appears as part of an issue basic message. *)
    Record t := {
      reserved_2 : list byte;
      serial_no : list byte;
      applicable_business_day : list byte;
      reserved_1 : list byte;
      issue_name : list byte;
      security_type_etc_identification_code : list byte;
      isin_flag : list byte;
      new_security_code : list byte;
      industry_code : list byte;
      new_listing_flag : list byte;
      when_issued_transaction_flag : list byte;
      short_selling_price_restriction_applied_flag_at_the_regular_distribution : list byte;
      loan_margin_flag : list byte;
      ex_dividend_ex_right_flag : list byte;
      securities_to_be_delisted_under_supervision_classification : list byte;
      reserved_5 : list byte;
      unit_of_trading : list byte;
      index_constituent_issue : IndexConstituentIssue.t;
      order_prohibition_status_at_the_regular_distribution : OrderProhibitionStatusAtTheRegularDistribution.t;
      reserved_11 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (serial_no record) = 6 /\
      Datatypes.length (applicable_business_day record) = 8 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (issue_name record) = 20 /\
      Datatypes.length (security_type_etc_identification_code record) = 2 /\
      Datatypes.length (isin_flag record) = 1 /\
      Datatypes.length (new_security_code record) = 12 /\
      Datatypes.length (industry_code record) = 4 /\
      Datatypes.length (new_listing_flag record) = 1 /\
      Datatypes.length (when_issued_transaction_flag record) = 1 /\
      Datatypes.length (short_selling_price_restriction_applied_flag_at_the_regular_distribution record) = 1 /\
      Datatypes.length (loan_margin_flag record) = 1 /\
      Datatypes.length (ex_dividend_ex_right_flag record) = 2 /\
      Datatypes.length (securities_to_be_delisted_under_supervision_classification record) = 1 /\
      Datatypes.length (reserved_5 record) = 5 /\
      Datatypes.length (unit_of_trading record) = 14 /\
      IndexConstituentIssue.bounded (index_constituent_issue record) /\
      OrderProhibitionStatusAtTheRegularDistribution.bounded (order_prohibition_status_at_the_regular_distribution record) /\
      Datatypes.length (reserved_11 record) = 11.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (serial_no record) ++
      encode_bytes 8 (applicable_business_day record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 20 (issue_name record) ++
      encode_bytes 2 (security_type_etc_identification_code record) ++
      encode_bytes 1 (isin_flag record) ++
      encode_bytes 12 (new_security_code record) ++
      encode_bytes 4 (industry_code record) ++
      encode_bytes 1 (new_listing_flag record) ++
      encode_bytes 1 (when_issued_transaction_flag record) ++
      encode_bytes 1 (short_selling_price_restriction_applied_flag_at_the_regular_distribution record) ++
      encode_bytes 1 (loan_margin_flag record) ++
      encode_bytes 2 (ex_dividend_ex_right_flag record) ++
      encode_bytes 1 (securities_to_be_delisted_under_supervision_classification record) ++
      encode_bytes 5 (reserved_5 record) ++
      encode_bytes 14 (unit_of_trading record) ++
      IndexConstituentIssue.encode (index_constituent_issue record) ++
      OrderProhibitionStatusAtTheRegularDistribution.encode (order_prohibition_status_at_the_regular_distribution record) ++
      encode_bytes 11 (reserved_11 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (serial_no_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (applicable_business_day_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (issue_name_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (security_type_etc_identification_code_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (isin_flag_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (new_security_code_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (industry_code_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (new_listing_flag_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (when_issued_transaction_flag_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (short_selling_price_restriction_applied_flag_at_the_regular_distribution_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (loan_margin_flag_value, bytes) =>
                                                          match decode_bytes 2 bytes with
                                                          | None => None
                                                          | Some (ex_dividend_ex_right_flag_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (securities_to_be_delisted_under_supervision_classification_value, bytes) =>
                                                                  match decode_bytes 5 bytes with
                                                                  | None => None
                                                                  | Some (reserved_5_value, bytes) =>
                                                                      match decode_bytes 14 bytes with
                                                                      | None => None
                                                                      | Some (unit_of_trading_value, bytes) =>
                                                                          match IndexConstituentIssue.decode bytes with
                                                                          | None => None
                                                                          | Some (index_constituent_issue_value, bytes) =>
                                                                              match OrderProhibitionStatusAtTheRegularDistribution.decode bytes with
                                                                              | None => None
                                                                              | Some (order_prohibition_status_at_the_regular_distribution_value, bytes) =>
                                                                                  match decode_bytes 11 bytes with
                                                                                  | None => None
                                                                                  | Some (reserved_11_value, bytes) =>
                                                                                      Some ({| reserved_2 := reserved_2_value; serial_no := serial_no_value; applicable_business_day := applicable_business_day_value; reserved_1 := reserved_1_value; issue_name := issue_name_value; security_type_etc_identification_code := security_type_etc_identification_code_value; isin_flag := isin_flag_value; new_security_code := new_security_code_value; industry_code := industry_code_value; new_listing_flag := new_listing_flag_value; when_issued_transaction_flag := when_issued_transaction_flag_value; short_selling_price_restriction_applied_flag_at_the_regular_distribution := short_selling_price_restriction_applied_flag_at_the_regular_distribution_value; loan_margin_flag := loan_margin_flag_value; ex_dividend_ex_right_flag := ex_dividend_ex_right_flag_value; securities_to_be_delisted_under_supervision_classification := securities_to_be_delisted_under_supervision_classification_value; reserved_5 := reserved_5_value; unit_of_trading := unit_of_trading_value; index_constituent_issue := index_constituent_issue_value; order_prohibition_status_at_the_regular_distribution := order_prohibition_status_at_the_regular_distribution_value; reserved_11 := reserved_11_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 123.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !IndexConstituentIssue.encode_length, !OrderProhibitionStatusAtTheRegularDistribution.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite IndexConstituentIssue.decode_encode by exact bound_17.
      rewrite OrderProhibitionStatusAtTheRegularDistribution.decode_encode by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IndexConstituentIssue.eq_dec | apply OrderProhibitionStatusAtTheRegularDistribution.eq_dec]. Defined.

  End IssueInformationMessage.

  Module BasePrice.

    (** Base Price *)
    Record t := {
      unit_flag : list byte;
      price : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (price record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (price record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; price := price_value; sign := sign_value |}, bytes)
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

  End BasePrice.

  Module LimitPriceMaximum.

    (** Limit Price (Maximum) *)
    Record t := {
      unit_flag : list byte;
      price : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (price record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (price record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; price := price_value; sign := sign_value |}, bytes)
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

  End LimitPriceMaximum.

  Module LimitPriceMinimum.

    (** Limit Price (Minimum) *)
    Record t := {
      unit_flag : list byte;
      price : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (price record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (price record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; price := price_value; sign := sign_value |}, bytes)
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

  End LimitPriceMinimum.

  Module BasePriceInformationMessage.

    (** In this Tag, the below items for the next business day or the day are set. This tag appears as part of an issue basic message. *)
    Record t := {
      reserved_2 : list byte;
      based_business_day : list byte;
      base_price : BasePrice.t;
      limit_price_maximum : LimitPriceMaximum.t;
      limit_price_minimum : LimitPriceMinimum.t;
      base_price_price_of_the_middle_of_the_book : list byte;
      number_of_tick_size_table : list byte;
      reserved_1 : list byte;
      reserved_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (based_business_day record) = 8 /\
      BasePrice.bounded (base_price record) /\
      LimitPriceMaximum.bounded (limit_price_maximum record) /\
      LimitPriceMinimum.bounded (limit_price_minimum record) /\
      Datatypes.length (base_price_price_of_the_middle_of_the_book record) = 1 /\
      Datatypes.length (number_of_tick_size_table record) = 2 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (reserved_4 record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 8 (based_business_day record) ++
      BasePrice.encode (base_price record) ++
      LimitPriceMaximum.encode (limit_price_maximum record) ++
      LimitPriceMinimum.encode (limit_price_minimum record) ++
      encode_bytes 1 (base_price_price_of_the_middle_of_the_book record) ++
      encode_bytes 2 (number_of_tick_size_table record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (based_business_day_value, bytes) =>
              match BasePrice.decode bytes with
              | None => None
              | Some (base_price_value, bytes) =>
                  match LimitPriceMaximum.decode bytes with
                  | None => None
                  | Some (limit_price_maximum_value, bytes) =>
                      match LimitPriceMinimum.decode bytes with
                      | None => None
                      | Some (limit_price_minimum_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (base_price_price_of_the_middle_of_the_book_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (number_of_tick_size_table_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (reserved_1_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (reserved_4_value, bytes) =>
                                          Some ({| reserved_2 := reserved_2_value; based_business_day := based_business_day_value; base_price := base_price_value; limit_price_maximum := limit_price_maximum_value; limit_price_minimum := limit_price_minimum_value; base_price_price_of_the_middle_of_the_book := base_price_price_of_the_middle_of_the_book_value; number_of_tick_size_table := number_of_tick_size_table_value; reserved_1 := reserved_1_value; reserved_4 := reserved_4_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !BasePrice.encode_length, !LimitPriceMaximum.encode_length, !LimitPriceMinimum.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite BasePrice.decode_encode by exact bound_2.
      rewrite LimitPriceMaximum.decode_encode by exact bound_3.
      rewrite LimitPriceMinimum.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply BasePrice.eq_dec | apply LimitPriceMaximum.eq_dec | apply LimitPriceMinimum.eq_dec]. Defined.

  End BasePriceInformationMessage.

  Module MulticastGroupNumberInformationMessage.

    (** In this tag, Multicast Group Number with which the issue is output is set. This tag appears as part of an Issue Realtime Message. *)
    Record t := {
      reserved_2 : list byte;
      applicable_business_day : list byte;
      issue_multicast_group_number : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (applicable_business_day record) = 8 /\
      Datatypes.length (issue_multicast_group_number record) = 3 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 8 (applicable_business_day record) ++
      encode_bytes 3 (issue_multicast_group_number record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (applicable_business_day_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (issue_multicast_group_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      Some ({| reserved_2 := reserved_2_value; applicable_business_day := applicable_business_day_value; issue_multicast_group_number := issue_multicast_group_number_value; reserved_1 := reserved_1_value |}, bytes)
                  end
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

  End MulticastGroupNumberInformationMessage.

  Module ControlMessage.

    (** In this tag, the Test Mode Flag and the Start/End Flag that are used in a Control Message will be set. This tag appears as part of a Control Message (Communication Control, Health Check Control, Stock Base Price Information Control, CB Base Price Information Control, Issue Information Control and Multicast Group Number Information Control). *)
    Record t := {
      reserved_2 : list byte;
      test_mode_flag : list byte;
      start_end_flag : list byte;
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (test_mode_flag record) = 1 /\
      Datatypes.length (start_end_flag record) = 1 /\
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 1 (test_mode_flag record) ++
      encode_bytes 1 (start_end_flag record) ++
      encode_bytes 6 (time record).

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
                  | Some (time_value, bytes) =>
                      Some ({| reserved_2 := reserved_2_value; test_mode_flag := test_mode_flag_value; start_end_flag := start_end_flag_value; time := time_value |}, bytes)
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

End TseEquitiesIssueBasicInformationV195.
