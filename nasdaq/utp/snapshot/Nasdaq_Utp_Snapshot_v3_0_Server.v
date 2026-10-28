From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Snapshot

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
      - the dispatch that chooses a message by its type
      - a field present only on a condition
      - a length prefix framing what follows
  *)

Module NasdaqUtpSnapshotV30Server.

  Module ServerTcpPacketHeader.

    (** Packet header of a packet sent by the server *)
    Record t := {
      packet_length : N;
      server_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (server_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (server_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (server_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; server_packet_type := server_packet_type_value |}, bytes)
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

  End ServerTcpPacketHeader.

  Module MessageHeader.

    (** UTP Snap-Shot message header — fixed Version + Message Category prefix *)
    Record t := {
      version : N;
      message_category : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (version record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (message_category record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (version record) ++
      encode_bytes 1 (message_category record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (version_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_category_value, bytes) =>
              Some ({| version := version_value; message_category := message_category_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End MessageHeader.

  Module IssueSymbolDirectoryMessage.

    (** Issue Symbol Directory Message providing reference data for NASDAQ-listed securities. To be retired in Q1 2027 in favor of the Enhanced Issue Symbol Directory Message (Type F). *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol : list byte;
      old_symbol : list byte;
      issue_name : list byte;
      issue_type : list byte;
      issue_subtype : list byte;
      market_tier : list byte;
      authenticity : list byte;
      short_sale_threshold_indicator : list byte;
      round_lot_size : N;
      financial_status_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 11 /\
      Datatypes.length (old_symbol record) = 11 /\
      Datatypes.length (issue_name record) = 30 /\
      Datatypes.length (issue_type record) = 1 /\
      Datatypes.length (issue_subtype record) = 2 /\
      Datatypes.length (market_tier record) = 1 /\
      Datatypes.length (authenticity record) = 1 /\
      Datatypes.length (short_sale_threshold_indicator record) = 1 /\
      (round_lot_size record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (financial_status_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol record) ++
      encode_bytes 11 (old_symbol record) ++
      encode_bytes 30 (issue_name record) ++
      encode_bytes 1 (issue_type record) ++
      encode_bytes 2 (issue_subtype record) ++
      encode_bytes 1 (market_tier record) ++
      encode_bytes 1 (authenticity record) ++
      encode_bytes 1 (short_sale_threshold_indicator record) ++
      encode_uint 2 (round_lot_size record) ++
      encode_bytes 1 (financial_status_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (old_symbol_value, bytes) =>
                                  match decode_bytes 30 bytes with
                                  | None => None
                                  | Some (issue_name_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (issue_type_value, bytes) =>
                                          match decode_bytes 2 bytes with
                                          | None => None
                                          | Some (issue_subtype_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (market_tier_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (authenticity_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (short_sale_threshold_indicator_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (round_lot_size_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (financial_status_indicator_value, bytes) =>
                                                                  Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol := symbol_value; old_symbol := old_symbol_value; issue_name := issue_name_value; issue_type := issue_type_value; issue_subtype := issue_subtype_value; market_tier := market_tier_value; authenticity := authenticity_value; short_sale_threshold_indicator := short_sale_threshold_indicator_value; round_lot_size := round_lot_size_value; financial_status_indicator := financial_status_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 87.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IssueSymbolDirectoryMessage.

  Module EnhancedIssueSymbolDirectoryMessage.

    (** Enhanced Issue Symbol Directory Message — introduced in v3.0 alongside the existing Issue Symbol Directory Message (Type B) to support the SEC MPI Tick Rule (Nov 2026) and Extended Operational Hours (Dec 6, 2026). Adds ETP/IPO/MPI/Trading-State/Halt-Reason/Reg-SHO fields and two RESERVED prior-close prices. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol : list byte;
      old_symbol : list byte;
      issue_name : list byte;
      issue_type : list byte;
      issue_subtype : list byte;
      market_tier : list byte;
      authenticity : list byte;
      short_sale_threshold_indicator : list byte;
      round_lot_size : N;
      financial_status_indicator : list byte;
      etp_indicator : list byte;
      new_issue_indicator : list byte;
      mpi_tick : list byte;
      trading_state : list byte;
      halt_reason : list byte;
      reg_sho_action : list byte;
      consolidated_prior_day_close_price : N;
      listing_market_official_prior_day_close_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 11 /\
      Datatypes.length (old_symbol record) = 11 /\
      Datatypes.length (issue_name record) = 30 /\
      Datatypes.length (issue_type record) = 1 /\
      Datatypes.length (issue_subtype record) = 2 /\
      Datatypes.length (market_tier record) = 1 /\
      Datatypes.length (authenticity record) = 1 /\
      Datatypes.length (short_sale_threshold_indicator record) = 1 /\
      (round_lot_size record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (etp_indicator record) = 1 /\
      Datatypes.length (new_issue_indicator record) = 1 /\
      Datatypes.length (mpi_tick record) = 1 /\
      Datatypes.length (trading_state record) = 1 /\
      Datatypes.length (halt_reason record) = 6 /\
      Datatypes.length (reg_sho_action record) = 1 /\
      (consolidated_prior_day_close_price record < 256 ^ N.of_nat 8)%N /\
      (listing_market_official_prior_day_close_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol record) ++
      encode_bytes 11 (old_symbol record) ++
      encode_bytes 30 (issue_name record) ++
      encode_bytes 1 (issue_type record) ++
      encode_bytes 2 (issue_subtype record) ++
      encode_bytes 1 (market_tier record) ++
      encode_bytes 1 (authenticity record) ++
      encode_bytes 1 (short_sale_threshold_indicator record) ++
      encode_uint 2 (round_lot_size record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 1 (etp_indicator record) ++
      encode_bytes 1 (new_issue_indicator record) ++
      encode_bytes 1 (mpi_tick record) ++
      encode_bytes 1 (trading_state record) ++
      encode_bytes 6 (halt_reason record) ++
      encode_bytes 1 (reg_sho_action record) ++
      encode_uint 8 (consolidated_prior_day_close_price record) ++
      encode_uint 8 (listing_market_official_prior_day_close_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (old_symbol_value, bytes) =>
                                  match decode_bytes 30 bytes with
                                  | None => None
                                  | Some (issue_name_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (issue_type_value, bytes) =>
                                          match decode_bytes 2 bytes with
                                          | None => None
                                          | Some (issue_subtype_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (market_tier_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (authenticity_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (short_sale_threshold_indicator_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (round_lot_size_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (financial_status_indicator_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (etp_indicator_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (new_issue_indicator_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (mpi_tick_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (trading_state_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (halt_reason_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (reg_sho_action_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (consolidated_prior_day_close_price_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (listing_market_official_prior_day_close_price_value, bytes) =>
                                                                                                  Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol := symbol_value; old_symbol := old_symbol_value; issue_name := issue_name_value; issue_type := issue_type_value; issue_subtype := issue_subtype_value; market_tier := market_tier_value; authenticity := authenticity_value; short_sale_threshold_indicator := short_sale_threshold_indicator_value; round_lot_size := round_lot_size_value; financial_status_indicator := financial_status_indicator_value; etp_indicator := etp_indicator_value; new_issue_indicator := new_issue_indicator_value; mpi_tick := mpi_tick_value; trading_state := trading_state_value; halt_reason := halt_reason_value; reg_sho_action := reg_sho_action_value; consolidated_prior_day_close_price := consolidated_prior_day_close_price_value; listing_market_official_prior_day_close_price := listing_market_official_prior_day_close_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 114.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EnhancedIssueSymbolDirectoryMessage.

  Module RegShoShortSalePriceTestRestrictedIndicatorMessage.

    (** Reg SHO Restriction Indicator Message indicating the Rule 201 status for NASDAQ-listed securities. Snap-Shot sends a full spin of all active securities reflecting the current Reg SHO Action. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 11 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (reg_sho_action_value, bytes) =>
                                  Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol := symbol_value; reg_sho_action := reg_sho_action_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegShoShortSalePriceTestRestrictedIndicatorMessage.

  Module CrossSroTradingActionMessage.

    (** Cross SRO Trading Action message. In Snap-Shot, sent only for NASDAQ-listed issues currently halted, in a Quote Resumption, or in a LULD pause. Absence implies the issue is eligible for normal quoting and trading. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol : list byte;
      trading_action_code : list byte;
      trading_action_sequence_number : N;
      action_time : N;
      reason_for_the_trading_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 11 /\
      Datatypes.length (trading_action_code record) = 1 /\
      (trading_action_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (action_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reason_for_the_trading_action record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol record) ++
      encode_bytes 1 (trading_action_code record) ++
      encode_uint 4 (trading_action_sequence_number record) ++
      encode_uint 8 (action_time record) ++
      encode_bytes 6 (reason_for_the_trading_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trading_action_code_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (trading_action_sequence_number_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (action_time_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (reason_for_the_trading_action_value, bytes) =>
                                              Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol := symbol_value; trading_action_code := trading_action_code_value; trading_action_sequence_number := trading_action_sequence_number_value; action_time := action_time_value; reason_for_the_trading_action := reason_for_the_trading_action_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CrossSroTradingActionMessage.

  Module MarketCenterTradingActionMessage.

    (** Market Center Trading Action message — sent when a UTP participant invokes or releases a market center-specific trading halt for a NASDAQ-listed security. Other participants may continue to quote and trade. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol : list byte;
      trading_action_code : list byte;
      action_time : N;
      market_center_identifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 11 /\
      Datatypes.length (trading_action_code record) = 1 /\
      (action_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_center_identifier record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol record) ++
      encode_bytes 1 (trading_action_code record) ++
      encode_uint 8 (action_time record) ++
      encode_bytes 1 (market_center_identifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trading_action_code_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (action_time_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (market_center_identifier_value, bytes) =>
                                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol := symbol_value; trading_action_code := trading_action_code_value; action_time := action_time_value; market_center_identifier := market_center_identifier_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketCenterTradingActionMessage.

  Module MarketWideCircuitBreakerDeclineLevelMessage.

    (** MWCB Decline Message. Communicates the daily MWCB breach points (Levels 1/2/3) set based on the prior day's closing value of the S&P 500 index. May be re-sent if levels are reset due to erroneous activity; participants should use the most recently disseminated values. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      mwcb_level_1 : N;
      mwcb_level_2 : N;
      mwcb_level_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_1 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_2 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_3 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_uint 8 (mwcb_level_1 record) ++
      encode_uint 8 (mwcb_level_2 record) ++
      encode_uint 8 (mwcb_level_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (mwcb_level_1_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (mwcb_level_2_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (mwcb_level_3_value, bytes) =>
                                      Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; mwcb_level_1 := mwcb_level_1_value; mwcb_level_2 := mwcb_level_2_value; mwcb_level_3 := mwcb_level_3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketWideCircuitBreakerDeclineLevelMessage.

  Module LimitUpLimitDownPriceBandMessage.

    (** Limit Up – Limit Down Price Band Message. Reflects the current LULD band for LULD-eligible securities. Designed to prevent trades outside specified Upper and Lower Limit Price Bands. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol : list byte;
      luld_price_band_indicator : list byte;
      luld_price_band_effective_time : N;
      limit_down_price : N;
      limit_up_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 11 /\
      Datatypes.length (luld_price_band_indicator record) = 1 /\
      (luld_price_band_effective_time record < 256 ^ N.of_nat 8)%N /\
      (limit_down_price record < 256 ^ N.of_nat 8)%N /\
      (limit_up_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol record) ++
      encode_bytes 1 (luld_price_band_indicator record) ++
      encode_uint 8 (luld_price_band_effective_time record) ++
      encode_uint 8 (limit_down_price record) ++
      encode_uint 8 (limit_up_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (luld_price_band_indicator_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (luld_price_band_effective_time_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (limit_down_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (limit_up_price_value, bytes) =>
                                              Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol := symbol_value; luld_price_band_indicator := luld_price_band_indicator_value; luld_price_band_effective_time := luld_price_band_effective_time_value; limit_down_price := limit_down_price_value; limit_up_price := limit_up_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LimitUpLimitDownPriceBandMessage.

  Module AuctionCollarMessage.

    (** Auction Collar Message published by primary markets using an automated reopening after a LULD Trading Pause. Snap-Shot sends only the most recent Auction Collar message per security. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol : list byte;
      trading_action_sequence_number : N;
      collar_reference_price : N;
      collar_up_price : N;
      collar_down_price : N;
      collar_extension_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 11 /\
      (trading_action_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (collar_reference_price record < 256 ^ N.of_nat 8)%N /\
      (collar_up_price record < 256 ^ N.of_nat 8)%N /\
      (collar_down_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (collar_extension_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol record) ++
      encode_uint 4 (trading_action_sequence_number record) ++
      encode_uint 8 (collar_reference_price record) ++
      encode_uint 8 (collar_up_price record) ++
      encode_uint 8 (collar_down_price record) ++
      encode_bytes 1 (collar_extension_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (trading_action_sequence_number_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (collar_reference_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (collar_up_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (collar_down_price_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (collar_extension_indicator_value, bytes) =>
                                                  Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol := symbol_value; trading_action_sequence_number := trading_action_sequence_number_value; collar_reference_price := collar_reference_price_value; collar_up_price := collar_up_price_value; collar_down_price := collar_down_price_value; collar_extension_indicator := collar_extension_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionCollarMessage.

  Module SnapshotSequenceMessage.

    (** Snapshot Sequence Number Message. Reflects the UTP Data Service sequence number at the time the UTP Snap-Shot spin was requested. To stay current, firms should process real-time UTP Data Service messages beginning with the next sequence number after this value. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      (sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_uint 8 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (sequence_number_value, bytes) =>
                              Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; sequence_number := sequence_number_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SnapshotSequenceMessage.

  Module StartOfDayMessage.

    (** Start of Day Control Message. Each day, signals that all subsequent data transmitted will be real-time updates. Prior to 03:58 the data feed handler may be broadcasting heartbeats. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StartOfDayMessage.

  Module MarketSessionOpenMessage.

    (** Market Session Open Control Message. Signifies the opening of market systems for the Normal Market Session. Each UTP participant may choose to provide its own Market Session Open control message. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSessionOpenMessage.

  Module MarketSessionCloseMessage.

    (** Market Session Close Control Message. Signals the closing of market systems for the Normal Market Session. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSessionCloseMessage.

  Module EndOfDayMessage.

    (** End of Day Control Message. Signals the end of active message dissemination for the UTP SIP operational cycle. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfDayMessage.

  Module EndOfTransmissionsMessage.

    (** End of Transmissions Control Message. Last production message of the day; signals no further transmissions through the UTP SIP line. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfTransmissionsMessage.

  Module LoginAcceptedPacket.

    (** SoupBinTCP Login Accepted Packet *)
    Record t := {
      accepted_session : list byte;
      accepted_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (accepted_session record) = 10 /\
      Datatypes.length (accepted_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (accepted_session record) ++
      encode_bytes 20 (accepted_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (accepted_session_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (accepted_sequence_number_value, bytes) =>
              Some ({| accepted_session := accepted_session_value; accepted_sequence_number := accepted_sequence_number_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginAcceptedPacket.

  Module LoginRejectedPacket.

    (** SoupBinTCP Login Rejected Packet *)
    Record t := {
      reject_reason_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reject_reason_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reject_reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reject_reason_code_value, bytes) =>
          Some ({| reject_reason_code := reject_reason_code_value |}, bytes)
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

  End LoginRejectedPacket.

End NasdaqUtpSnapshotV30Server.
