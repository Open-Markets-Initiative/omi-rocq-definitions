From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsa Mexicana de Valores Bmv Market Data Product 22

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
      - a run counted by a field

    License: MIT No Attribution
  *)

Module BmvMarketDataProduct22V11.

  Module INTRAMulticastHeader.

    (** BMV INTRA Multicast Header *)
    Record t := {
      length_ : N;
      total_messages : N;
      market_data_group : N;
      session : N;
      sequence_number : N;
      datetime : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (total_messages record < 256 ^ N.of_nat 1)%N /\
      (market_data_group record < 256 ^ N.of_nat 1)%N /\
      (session record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (datetime record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (total_messages record) ++
      encode_uint 1 (market_data_group record) ++
      encode_uint 1 (session record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (total_messages_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (market_data_group_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (session_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (sequence_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (datetime_value, bytes) =>
                              Some ({| length_ := length__value; total_messages := total_messages_value; market_data_group := market_data_group_value; session := session_value; sequence_number := sequence_number_value; datetime := datetime_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End INTRAMulticastHeader.

  Module MessageHeader.

    (** Message length and message type *)
    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  Module EventsSystemMessage.

    (** The system of events message is used to inform that an event has occurred, which needs to be of public domain. *)
    Record t := {
      instrument_number : N;
      event_code : list byte;
      market : list byte;
      sending_time : N;
      ending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1 /\
      Datatypes.length (market record) = 1 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (ending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (event_code record) ++
      encode_bytes 1 (market record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (ending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (sending_time_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (ending_time_value, bytes) =>
                          Some ({| instrument_number := instrument_number_value; event_code := event_code_value; market := market_value; sending_time := sending_time_value; ending_time := ending_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EventsSystemMessage.

  Module DollarBuySellMessage.

    (** Dollar Buy/Sell *)
    Record t := {
      posture_date : N;
      currency : list byte;
      dollar_side : list byte;
      buy : N;
      sell : N;
      last_deal : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (posture_date record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (currency record) = 5 /\
      Datatypes.length (dollar_side record) = 1 /\
      (buy record < 256 ^ N.of_nat 8)%N /\
      (sell record < 256 ^ N.of_nat 8)%N /\
      (last_deal record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (posture_date record) ++
      encode_bytes 5 (currency record) ++
      encode_bytes 1 (dollar_side record) ++
      encode_uint 8 (buy record) ++
      encode_uint 8 (sell record) ++
      encode_uint 8 (last_deal record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (posture_date_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (currency_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (dollar_side_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (buy_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sell_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (last_deal_value, bytes) =>
                              Some ({| posture_date := posture_date_value; currency := currency_value; dollar_side := dollar_side_value; buy := buy_value; sell := sell_value; last_deal := last_deal_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DollarBuySellMessage.

  Module ShortSalesBalancesPerInstrumentMessage.

    (** Short sales balances per instrument *)
    Record t := {
      instrument_number : N;
      date : N;
      previous_balance : N;
      amount_traded : N;
      buybacks : N;
      current_balance : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (date record < 256 ^ N.of_nat 8)%N /\
      (previous_balance record < 256 ^ N.of_nat 8)%N /\
      (amount_traded record < 256 ^ N.of_nat 8)%N /\
      (buybacks record < 256 ^ N.of_nat 8)%N /\
      (current_balance record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (date record) ++
      encode_uint 8 (previous_balance record) ++
      encode_uint 8 (amount_traded record) ++
      encode_uint 8 (buybacks record) ++
      encode_uint 8 (current_balance record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (date_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (previous_balance_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (amount_traded_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (buybacks_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (current_balance_value, bytes) =>
                              Some ({| instrument_number := instrument_number_value; date := date_value; previous_balance := previous_balance_value; amount_traded := amount_traded_value; buybacks := buybacks_value; current_balance := current_balance_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ShortSalesBalancesPerInstrumentMessage.

  Module CapitalMarketMultiplesMessage.

    (** Capital Market Multiples *)
    Record t := {
      instrument_id : N;
      multiple_type : list byte;
      registry_number : list byte;
      sector : N;
      subsector : N;
      business_line : N;
      sub_line : N;
      pflepa_multiple : N;
      pfepa_multiple : N;
      ve_uaiida_multiple : N;
      p_u : N;
      p_vl : N;
      f_1_p_unoc : N;
      f_2_p_unoc : N;
      f_1_p_ue : N;
      f_2_p_ue : N;
      f_1_ve_uaiida : N;
      f_2_ve_uaiida : N;
      f_1_p_u : N;
      f_2_p_u : N;
      f_1_p_vl : N;
      f_2_p_vl : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (multiple_type record) = 1 /\
      Datatypes.length (registry_number record) = 1 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (subsector record < 256 ^ N.of_nat 1)%N /\
      (business_line record < 256 ^ N.of_nat 1)%N /\
      (sub_line record < 256 ^ N.of_nat 1)%N /\
      (pflepa_multiple record < 256 ^ N.of_nat 8)%N /\
      (pfepa_multiple record < 256 ^ N.of_nat 8)%N /\
      (ve_uaiida_multiple record < 256 ^ N.of_nat 8)%N /\
      (p_u record < 256 ^ N.of_nat 8)%N /\
      (p_vl record < 256 ^ N.of_nat 8)%N /\
      (f_1_p_unoc record < 256 ^ N.of_nat 8)%N /\
      (f_2_p_unoc record < 256 ^ N.of_nat 8)%N /\
      (f_1_p_ue record < 256 ^ N.of_nat 8)%N /\
      (f_2_p_ue record < 256 ^ N.of_nat 8)%N /\
      (f_1_ve_uaiida record < 256 ^ N.of_nat 8)%N /\
      (f_2_ve_uaiida record < 256 ^ N.of_nat 8)%N /\
      (f_1_p_u record < 256 ^ N.of_nat 8)%N /\
      (f_2_p_u record < 256 ^ N.of_nat 8)%N /\
      (f_1_p_vl record < 256 ^ N.of_nat 8)%N /\
      (f_2_p_vl record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (multiple_type record) ++
      encode_bytes 1 (registry_number record) ++
      encode_uint 1 (sector record) ++
      encode_uint 1 (subsector record) ++
      encode_uint 1 (business_line record) ++
      encode_uint 1 (sub_line record) ++
      encode_uint 8 (pflepa_multiple record) ++
      encode_uint 8 (pfepa_multiple record) ++
      encode_uint 8 (ve_uaiida_multiple record) ++
      encode_uint 8 (p_u record) ++
      encode_uint 8 (p_vl record) ++
      encode_uint 8 (f_1_p_unoc record) ++
      encode_uint 8 (f_2_p_unoc record) ++
      encode_uint 8 (f_1_p_ue record) ++
      encode_uint 8 (f_2_p_ue record) ++
      encode_uint 8 (f_1_ve_uaiida record) ++
      encode_uint 8 (f_2_ve_uaiida record) ++
      encode_uint 8 (f_1_p_u record) ++
      encode_uint 8 (f_2_p_u record) ++
      encode_uint 8 (f_1_p_vl record) ++
      encode_uint 8 (f_2_p_vl record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (multiple_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (registry_number_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (sector_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (subsector_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (business_line_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (sub_line_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (pflepa_multiple_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (pfepa_multiple_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (ve_uaiida_multiple_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (p_u_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (p_vl_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (f_1_p_unoc_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (f_2_p_unoc_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (f_1_p_ue_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (f_2_p_ue_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (f_1_ve_uaiida_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (f_2_ve_uaiida_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (f_1_p_u_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (f_2_p_u_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (f_1_p_vl_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (f_2_p_vl_value, bytes) =>
                                                                                              Some ({| instrument_id := instrument_id_value; multiple_type := multiple_type_value; registry_number := registry_number_value; sector := sector_value; subsector := subsector_value; business_line := business_line_value; sub_line := sub_line_value; pflepa_multiple := pflepa_multiple_value; pfepa_multiple := pfepa_multiple_value; ve_uaiida_multiple := ve_uaiida_multiple_value; p_u := p_u_value; p_vl := p_vl_value; f_1_p_unoc := f_1_p_unoc_value; f_2_p_unoc := f_2_p_unoc_value; f_1_p_ue := f_1_p_ue_value; f_2_p_ue := f_2_p_ue_value; f_1_ve_uaiida := f_1_ve_uaiida_value; f_2_ve_uaiida := f_2_ve_uaiida_value; f_1_p_u := f_1_p_u_value; f_2_p_u := f_2_p_u_value; f_1_p_vl := f_1_p_vl_value; f_2_p_vl := f_2_p_vl_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 130.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 bound_21]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
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
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CapitalMarketMultiplesMessage.

  Module CapitalizationRulesMessage.

    (** Capitalization Rules *)
    Record t := {
      instrument_number : N;
      date_indicators : N;
      bursatility_indices : N;
      bursatility_indices_sign : list byte;
      beta_coefficient : N;
      beta_coefficient_sign : list byte;
      correlation_coefficient : N;
      correlation_coefficient_sign : list byte;
      delta_difference : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (date_indicators record < 256 ^ N.of_nat 8)%N /\
      (bursatility_indices record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bursatility_indices_sign record) = 1 /\
      (beta_coefficient record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (beta_coefficient_sign record) = 1 /\
      (correlation_coefficient record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (correlation_coefficient_sign record) = 1 /\
      (delta_difference record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (date_indicators record) ++
      encode_uint 4 (bursatility_indices record) ++
      encode_bytes 1 (bursatility_indices_sign record) ++
      encode_uint 8 (beta_coefficient record) ++
      encode_bytes 1 (beta_coefficient_sign record) ++
      encode_uint 8 (correlation_coefficient record) ++
      encode_bytes 1 (correlation_coefficient_sign record) ++
      encode_uint 4 (delta_difference record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (date_indicators_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (bursatility_indices_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (bursatility_indices_sign_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (beta_coefficient_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (beta_coefficient_sign_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (correlation_coefficient_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (correlation_coefficient_sign_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (delta_difference_value, bytes) =>
                                          Some ({| instrument_number := instrument_number_value; date_indicators := date_indicators_value; bursatility_indices := bursatility_indices_value; bursatility_indices_sign := bursatility_indices_sign_value; beta_coefficient := beta_coefficient_value; beta_coefficient_sign := beta_coefficient_sign_value; correlation_coefficient := correlation_coefficient_value; correlation_coefficient_sign := correlation_coefficient_sign_value; delta_difference := delta_difference_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CapitalizationRulesMessage.

End BmvMarketDataProduct22V11.
