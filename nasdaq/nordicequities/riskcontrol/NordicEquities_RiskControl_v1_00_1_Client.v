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

Module NordicEquitiesRiskControlV1001Client.

  Module ClientPacketHeader.

    (** Packet header of a packet sent by the client *)
    Record t := {
      packet_length : N;
      client_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (client_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (client_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (client_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; client_packet_type := client_packet_type_value |}, bytes)
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

  End ClientPacketHeader.

  Module LoginRequestPacket.

    (** The SoupBinTCP client must send a Login Request Packet immediately upon establishing a new TCP/IP socket connection to the server *)
    Record t := {
      username : list byte;
      password : list byte;
      requested_session : list byte;
      requested_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 6 /\
      Datatypes.length (password record) = 10 /\
      Datatypes.length (requested_session record) = 10 /\
      Datatypes.length (requested_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 10 (requested_session record) ++
      encode_bytes 20 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (requested_session_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (requested_sequence_number_value, bytes) =>
                      Some ({| username := username_value; password := password_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
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

  End LoginRequestPacket.

  Module ModifyAccountSettingsMessage.

    (** Updates the settings for a given PRM Account *)
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

  End ModifyAccountSettingsMessage.

  Module ModifyOrderBookRestrictionMessage.

    (** Marks an Order Book as restricted or non-restricted for a given PRM Account *)
    Record t := {
      user_ref_num : N;
      prm_account : list byte;
      order_book : N;
      state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_ref_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (prm_account record) = 6 /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_ref_num record) ++
      encode_bytes 6 (prm_account record) ++
      encode_uint 4 (order_book record) ++
      encode_bytes 1 (state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_ref_num_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (prm_account_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (state_value, bytes) =>
                      Some ({| user_ref_num := user_ref_num_value; prm_account := prm_account_value; order_book := order_book_value; state := state_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrderBookRestrictionMessage.

  Module ModifyMarketSegmentRestrictionMessage.

    (** Marks a Market Segment as restricted or non-restricted for a given PRM Account *)
    Record t := {
      user_ref_num : N;
      prm_account : list byte;
      market_segment : N;
      state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_ref_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (prm_account record) = 6 /\
      (market_segment record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_ref_num record) ++
      encode_bytes 6 (prm_account record) ++
      encode_uint 2 (market_segment record) ++
      encode_bytes 1 (state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_ref_num_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (prm_account_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (market_segment_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (state_value, bytes) =>
                      Some ({| user_ref_num := user_ref_num_value; prm_account := prm_account_value; market_segment := market_segment_value; state := state_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyMarketSegmentRestrictionMessage.

  Module ModifyLimitSettingsMessage.

    (** Updates the Limit settings for a given PRM Account and Currency *)
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

  End ModifyLimitSettingsMessage.

  Module ModifyAccountCurrencySettingMessage.

    (** Updates the settings for a given PRM Account's currency *)
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

  End ModifyAccountCurrencySettingMessage.

End NordicEquitiesRiskControlV1001Client.
