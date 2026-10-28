From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Nordic Pre-Trade Risk Management

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
      - a length prefix framing what follows
  *)

Module NordicEquitiesRiskControlV1001Server.

  Module ServerPacketHeader.

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

  End ServerPacketHeader.

  Module LoginAcceptedPacket.

    (** The SoupBinTCP server sends a Login Accepted Packet in response to receiving a valid Login Request from the client *)
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

    (** The SoupBinTCP server sends this packet in response to an invalid Login Request Packet from the client *)
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

  Module AccountQueryResponseMessage.

    (** Provides the PRM API port's next expected user reference number *)
    Record t := {
      user_ref_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_ref_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_ref_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_ref_num_value, bytes) =>
          Some ({| user_ref_num := user_ref_num_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AccountQueryResponseMessage.

  Module AccountSettingsResponseMessage.

    (** Indicates that the settings for a given PRM Account have been updated *)
    Record t := {
      user_ref_num : N;
      prm_account : list byte;
      repeated_order_generation : N;
      trigger_restrict_symbol_on_repeated_order_generation : list byte;
      in_auction_market_order_prevention : list byte;
      in_auction_fat_finger_protection : list byte;
      in_auction_market_order_protection : list byte;
      block_and_cancel : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_ref_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (prm_account record) = 6 /\
      (repeated_order_generation record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trigger_restrict_symbol_on_repeated_order_generation record) = 1 /\
      Datatypes.length (in_auction_market_order_prevention record) = 1 /\
      Datatypes.length (in_auction_fat_finger_protection record) = 1 /\
      Datatypes.length (in_auction_market_order_protection record) = 1 /\
      Datatypes.length (block_and_cancel record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_ref_num record) ++
      encode_bytes 6 (prm_account record) ++
      encode_uint 4 (repeated_order_generation record) ++
      encode_bytes 1 (trigger_restrict_symbol_on_repeated_order_generation record) ++
      encode_bytes 1 (in_auction_market_order_prevention record) ++
      encode_bytes 1 (in_auction_fat_finger_protection record) ++
      encode_bytes 1 (in_auction_market_order_protection record) ++
      encode_bytes 1 (block_and_cancel record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_ref_num_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (prm_account_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (repeated_order_generation_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trigger_restrict_symbol_on_repeated_order_generation_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (in_auction_market_order_prevention_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (in_auction_fat_finger_protection_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (in_auction_market_order_protection_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (block_and_cancel_value, bytes) =>
                                      Some ({| user_ref_num := user_ref_num_value; prm_account := prm_account_value; repeated_order_generation := repeated_order_generation_value; trigger_restrict_symbol_on_repeated_order_generation := trigger_restrict_symbol_on_repeated_order_generation_value; in_auction_market_order_prevention := in_auction_market_order_prevention_value; in_auction_fat_finger_protection := in_auction_fat_finger_protection_value; in_auction_market_order_protection := in_auction_market_order_protection_value; block_and_cancel := block_and_cancel_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AccountSettingsResponseMessage.

  Module OrderBookRestrictionResponseMessage.

    (** Indicates that an Order Book has been restricted or non-restricted for a given PRM Account *)
    Record t := {
      user_ref_num : N;
      timestamp : N;
      prm_account : list byte;
      order_book : N;
      state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_ref_num record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (prm_account record) = 6 /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_ref_num record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (prm_account record) ++
      encode_uint 4 (order_book record) ++
      encode_bytes 1 (state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_ref_num_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (prm_account_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_book_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (state_value, bytes) =>
                          Some ({| user_ref_num := user_ref_num_value; timestamp := timestamp_value; prm_account := prm_account_value; order_book := order_book_value; state := state_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookRestrictionResponseMessage.

  Module MarketSegmentRestrictionResponseMessage.

    (** Indicates that a Market Segment has been restricted or non-restricted for a given PRM Account *)
    Record t := {
      user_ref_num : N;
      timestamp : N;
      prm_account : list byte;
      market_segment : N;
      state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_ref_num record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (prm_account record) = 6 /\
      (market_segment record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_ref_num record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (prm_account record) ++
      encode_uint 2 (market_segment record) ++
      encode_bytes 1 (state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_ref_num_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (prm_account_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (market_segment_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (state_value, bytes) =>
                          Some ({| user_ref_num := user_ref_num_value; timestamp := timestamp_value; prm_account := prm_account_value; market_segment := market_segment_value; state := state_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSegmentRestrictionResponseMessage.

  Module LimitSettingsResponseMessage.

    (** Indicates that the Limit settings for a given PRM Account and Currency have been updated *)
    Record t := {
      user_ref_num : N;
      prm_account : list byte;
      currency : list byte;
      max_quantity : N;
      max_value : N;
      unused : N;
      total_risk_value : N;
      trade_buy_value : N;
      trade_sell_value : N;
      trade_net_value : N;
      open_order_buy_value : N;
      open_order_sell_value : N;
      open_order_net_value : N;
      max_quantity_auction : N;
      max_value_auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_ref_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (prm_account record) = 6 /\
      Datatypes.length (currency record) = 3 /\
      (max_quantity record < 256 ^ N.of_nat 8)%N /\
      (max_value record < 256 ^ N.of_nat 8)%N /\
      (unused record < 256 ^ N.of_nat 8)%N /\
      (total_risk_value record < 256 ^ N.of_nat 8)%N /\
      (trade_buy_value record < 256 ^ N.of_nat 8)%N /\
      (trade_sell_value record < 256 ^ N.of_nat 8)%N /\
      (trade_net_value record < 256 ^ N.of_nat 8)%N /\
      (open_order_buy_value record < 256 ^ N.of_nat 8)%N /\
      (open_order_sell_value record < 256 ^ N.of_nat 8)%N /\
      (open_order_net_value record < 256 ^ N.of_nat 8)%N /\
      (max_quantity_auction record < 256 ^ N.of_nat 8)%N /\
      (max_value_auction record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_ref_num record) ++
      encode_bytes 6 (prm_account record) ++
      encode_bytes 3 (currency record) ++
      encode_uint 8 (max_quantity record) ++
      encode_uint 8 (max_value record) ++
      encode_uint 8 (unused record) ++
      encode_uint 8 (total_risk_value record) ++
      encode_uint 8 (trade_buy_value record) ++
      encode_uint 8 (trade_sell_value record) ++
      encode_uint 8 (trade_net_value record) ++
      encode_uint 8 (open_order_buy_value record) ++
      encode_uint 8 (open_order_sell_value record) ++
      encode_uint 8 (open_order_net_value record) ++
      encode_uint 8 (max_quantity_auction record) ++
      encode_uint 8 (max_value_auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_ref_num_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (prm_account_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (currency_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (max_quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (max_value_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (unused_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (total_risk_value_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trade_buy_value_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_sell_value_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (trade_net_value_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (open_order_buy_value_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (open_order_sell_value_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (open_order_net_value_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (max_quantity_auction_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (max_value_auction_value, bytes) =>
                                                                  Some ({| user_ref_num := user_ref_num_value; prm_account := prm_account_value; currency := currency_value; max_quantity := max_quantity_value; max_value := max_value_value; unused := unused_value; total_risk_value := total_risk_value_value; trade_buy_value := trade_buy_value_value; trade_sell_value := trade_sell_value_value; trade_net_value := trade_net_value_value; open_order_buy_value := open_order_buy_value_value; open_order_sell_value := open_order_sell_value_value; open_order_net_value := open_order_net_value_value; max_quantity_auction := max_quantity_auction_value; max_value_auction := max_value_auction_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LimitSettingsResponseMessage.

  Module AccountCurrencySettingResponseMessage.

    (** Indicates that the settings for a given PRM Account's currency have been updated *)
    Record t := {
      user_ref_num : N;
      prm_account : list byte;
      currency : list byte;
      reject_all_flag : list byte;
      blow_through_protection : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_ref_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (prm_account record) = 6 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (reject_all_flag record) = 1 /\
      Datatypes.length (blow_through_protection record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_ref_num record) ++
      encode_bytes 6 (prm_account record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (reject_all_flag record) ++
      encode_bytes 1 (blow_through_protection record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_ref_num_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (prm_account_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (currency_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reject_all_flag_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (blow_through_protection_value, bytes) =>
                          Some ({| user_ref_num := user_ref_num_value; prm_account := prm_account_value; currency := currency_value; reject_all_flag := reject_all_flag_value; blow_through_protection := blow_through_protection_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AccountCurrencySettingResponseMessage.

  Module RejectMessage.

    (** Indicates that an inbound message has been rejected *)
    Record t := {
      user_ref_num : N;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_ref_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_ref_num record) ++
      encode_bytes 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_ref_num_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reason_value, bytes) =>
              Some ({| user_ref_num := user_ref_num_value; reason := reason_value |}, bytes)
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

  End RejectMessage.

  Module ApiPortRateBreachMessage.

    (** Indicates that the port's rate limit has been breached *)
    Record t := {
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          Some ({| timestamp := timestamp_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ApiPortRateBreachMessage.

  Module AccountRateBreachMessage.

    (** Indicates that a PRM Account's rate limit has been breached *)
    Record t := {
      timestamp : N;
      state : list byte;
      prm_account : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (state record) = 1 /\
      Datatypes.length (prm_account record) = 6.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (state record) ++
      encode_bytes 6 (prm_account record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (state_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (prm_account_value, bytes) =>
                  Some ({| timestamp := timestamp_value; state := state_value; prm_account := prm_account_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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

  End AccountRateBreachMessage.

  Module AccumulatedValuesMessage.

    (** Indicates the current Accumulated Values for a PRM Account and Currency, sent after order or trade updates *)
    Record t := {
      prm_account : list byte;
      currency : list byte;
      last_update_time : N;
      risk_total_value : N;
      trades_buy_value : N;
      trades_sell_value : N;
      trades_total_value : N;
      orders_buy_value : N;
      orders_sell_value : N;
      orders_total_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (prm_account record) = 6 /\
      Datatypes.length (currency record) = 3 /\
      (last_update_time record < 256 ^ N.of_nat 8)%N /\
      (risk_total_value record < 256 ^ N.of_nat 8)%N /\
      (trades_buy_value record < 256 ^ N.of_nat 8)%N /\
      (trades_sell_value record < 256 ^ N.of_nat 8)%N /\
      (trades_total_value record < 256 ^ N.of_nat 8)%N /\
      (orders_buy_value record < 256 ^ N.of_nat 8)%N /\
      (orders_sell_value record < 256 ^ N.of_nat 8)%N /\
      (orders_total_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (prm_account record) ++
      encode_bytes 3 (currency record) ++
      encode_uint 8 (last_update_time record) ++
      encode_uint 8 (risk_total_value record) ++
      encode_uint 8 (trades_buy_value record) ++
      encode_uint 8 (trades_sell_value record) ++
      encode_uint 8 (trades_total_value record) ++
      encode_uint 8 (orders_buy_value record) ++
      encode_uint 8 (orders_sell_value record) ++
      encode_uint 8 (orders_total_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (prm_account_value, bytes) =>
          match decode_bytes 3 bytes with
          | None => None
          | Some (currency_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_update_time_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (risk_total_value_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trades_buy_value_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (trades_sell_value_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (trades_total_value_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (orders_buy_value_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (orders_sell_value_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (orders_total_value_value, bytes) =>
                                              Some ({| prm_account := prm_account_value; currency := currency_value; last_update_time := last_update_time_value; risk_total_value := risk_total_value_value; trades_buy_value := trades_buy_value_value; trades_sell_value := trades_sell_value_value; trades_total_value := trades_total_value_value; orders_buy_value := orders_buy_value_value; orders_sell_value := orders_sell_value_value; orders_total_value := orders_total_value_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 73.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AccumulatedValuesMessage.

End NordicEquitiesRiskControlV1001Server.
