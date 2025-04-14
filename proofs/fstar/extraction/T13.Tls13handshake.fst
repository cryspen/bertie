module t13.Tls13handshake
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open t13.Tls13utils in
  let open Rand_core in
  ()

let algs_post_client_hello (st: t_ClientPostClientHello) = st._1

let algs_post_server_hello (st: t_ClientPostServerHello) = st._2

let algs_post_client_finished (st: t_ClientPostClientFinished) = st._2

let compute_psk_binder_zero_rtt
      (algs0: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
      (psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (tx: t13.Tls13formats.t_Transcript)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let
  { t13.Tls13crypto.f_hash = ha ;
    t13.Tls13crypto.f_aead = ae ;
    t13.Tls13crypto.f_signature = e_sa ;
    t13.Tls13crypto.f_kem = e_ks ;
    t13.Tls13crypto.f_psk_mode = psk_mode ;
    t13.Tls13crypto.f_zero_rtt = zero_rtt }:t13.Tls13crypto.t_Algorithms =
    algs0
  in
  match
    psk_mode, psk, (cast (trunc_len <: usize) <: u8)
    <:
    (bool & Core.Option.t_Option t13.Tls13utils.t_Bytes & u8)
  with
  | true, Core.Option.Option_Some k, _ ->
    let psk_handle:t13.Tls13keyscheduler.Key_schedule.t_Handle =
      {
        t13.Tls13keyscheduler.Key_schedule.f_name
        =
        t13.Tls13keyscheduler.Key_schedule.TLSnames_PSK
        <:
        t13.Tls13keyscheduler.Key_schedule.t_TLSnames;
        t13.Tls13keyscheduler.Key_schedule.f_alg = ha;
        t13.Tls13keyscheduler.Key_schedule.f_level = mk_u8 0
      }
      <:
      t13.Tls13keyscheduler.Key_schedule.t_Handle
    in
    let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler =
      t13.Tls13keyscheduler.Key_schedule.set_by_handle ks
        psk_handle
        (Core.Clone.f_clone #t13.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve k
          <:
          t13.Tls13utils.t_Bytes)
    in
    (match
        t13.Tls13formats.impl_Transcript__transcript_hash_without_client_hello tx ch trunc_len
        <:
        Core.Result.t_Result t13.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok th_trunc ->
        let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8) =
          t13.Tls13keyscheduler.derive_binder_key ha psk_handle ks
        in
        let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
        (match out <: Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8 with
          | Core.Result.Result_Ok mk_handle ->
            let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8) =
              t13.Tls13keyscheduler.Key_schedule.v_XPD ks
                (t13.Tls13keyscheduler.Key_schedule.TLSnames_Binder
                  <:
                  t13.Tls13keyscheduler.Key_schedule.t_TLSnames)
                (mk_u8 0)
                mk_handle
                true
                th_trunc
            in
            let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
            (match
                out <: Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8
              with
              | Core.Result.Result_Ok binder_handle ->
                (match
                    t13.Tls13keyscheduler.Key_schedule.tagkey_from_handle ks binder_handle
                    <:
                    Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_TagKey u8
                  with
                  | Core.Result.Result_Ok hoist98 ->
                    let binder:t13.Tls13utils.t_Bytes =
                      hoist98.t13.Tls13keyscheduler.Key_schedule.f_val
                    in
                    (match
                        t13.Tls13formats.set_client_hello_binder algs0
                          (Core.Option.Option_Some binder
                            <:
                            Core.Option.t_Option t13.Tls13utils.t_Bytes)
                          ch
                          (Core.Option.Option_Some trunc_len <: Core.Option.t_Option usize)
                        <:
                        Core.Result.t_Result t13.Tls13formats.Handshake_data.t_HandshakeData u8
                      with
                      | Core.Result.Result_Ok nch ->
                        let tx_ch:t13.Tls13formats.t_Transcript =
                          t13.Tls13formats.impl_Transcript__add tx nch
                        in
                        if zero_rtt
                        then
                          match
                            t13.Tls13formats.impl_Transcript__transcript_hash tx_ch
                            <:
                            Core.Result.t_Result t13.Tls13utils.t_Bytes u8
                          with
                          | Core.Result.Result_Ok th ->
                            let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                              Core.Result.t_Result
                                (t13.Tls13crypto.t_AeadKeyIV &
                                  t13.Tls13keyscheduler.Key_schedule.t_Handle) u8) =
                              t13.Tls13keyscheduler.derive_0rtt_keys ha ae psk_handle th ks
                            in
                            let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                            (match
                                out
                                <:
                                Core.Result.t_Result
                                  (t13.Tls13crypto.t_AeadKeyIV &
                                    t13.Tls13keyscheduler.Key_schedule.t_Handle) u8
                              with
                              | Core.Result.Result_Ok (aek, handle) ->
                                (match
                                    t13.Tls13keyscheduler.Key_schedule.tagkey_from_handle ks
                                      handle
                                    <:
                                    Core.Result.t_Result
                                      t13.Tls13keyscheduler.Key_schedule.t_TagKey u8
                                  with
                                  | Core.Result.Result_Ok key ->
                                    let cipher0:Core.Option.t_Option
                                    t13.Tls13record.t_ClientCipherState0 =
                                      Core.Option.Option_Some
                                      (t13.Tls13record.client_cipher_state0 ae aek (mk_u64 0) key
                                      )
                                      <:
                                      Core.Option.t_Option t13.Tls13record.t_ClientCipherState0
                                    in
                                    ks,
                                    (Core.Result.Result_Ok
                                      (nch, cipher0, tx_ch
                                        <:
                                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                          Core.Option.t_Option
                                          t13.Tls13record.t_ClientCipherState0 &
                                          t13.Tls13formats.t_Transcript))
                                      <:
                                      Core.Result.t_Result
                                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                          Core.Option.t_Option
                                          t13.Tls13record.t_ClientCipherState0 &
                                          t13.Tls13formats.t_Transcript) u8)
                                    <:
                                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                                      Core.Result.t_Result
                                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                          Core.Option.t_Option
                                          t13.Tls13record.t_ClientCipherState0 &
                                          t13.Tls13formats.t_Transcript) u8)
                                  | Core.Result.Result_Err err ->
                                    ks,
                                    (Core.Result.Result_Err err
                                      <:
                                      Core.Result.t_Result
                                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                          Core.Option.t_Option
                                          t13.Tls13record.t_ClientCipherState0 &
                                          t13.Tls13formats.t_Transcript) u8)
                                    <:
                                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                                      Core.Result.t_Result
                                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                          Core.Option.t_Option
                                          t13.Tls13record.t_ClientCipherState0 &
                                          t13.Tls13formats.t_Transcript) u8))
                              | Core.Result.Result_Err err ->
                                ks,
                                (Core.Result.Result_Err err
                                  <:
                                  Core.Result.t_Result
                                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                      Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                                      t13.Tls13formats.t_Transcript) u8)
                                <:
                                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                                  Core.Result.t_Result
                                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                      Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                                      t13.Tls13formats.t_Transcript) u8))
                          | Core.Result.Result_Err err ->
                            ks,
                            (Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result
                                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                                  t13.Tls13formats.t_Transcript) u8)
                            <:
                            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                              Core.Result.t_Result
                                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                                  t13.Tls13formats.t_Transcript) u8)
                        else
                          ks,
                          (Core.Result.Result_Ok
                            (nch,
                              (Core.Option.Option_None
                                <:
                                Core.Option.t_Option t13.Tls13record.t_ClientCipherState0),
                              tx_ch
                              <:
                              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                                t13.Tls13formats.t_Transcript))
                            <:
                            Core.Result.t_Result
                              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                                t13.Tls13formats.t_Transcript) u8)
                          <:
                          (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                            Core.Result.t_Result
                              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                                t13.Tls13formats.t_Transcript) u8)
                      | Core.Result.Result_Err err ->
                        ks,
                        (Core.Result.Result_Err err
                          <:
                          Core.Result.t_Result
                            (t13.Tls13formats.Handshake_data.t_HandshakeData &
                              Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                              t13.Tls13formats.t_Transcript) u8)
                        <:
                        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                          Core.Result.t_Result
                            (t13.Tls13formats.Handshake_data.t_HandshakeData &
                              Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                              t13.Tls13formats.t_Transcript) u8))
                  | Core.Result.Result_Err err ->
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                          t13.Tls13formats.t_Transcript) u8)
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                          t13.Tls13formats.t_Transcript) u8))
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                      t13.Tls13formats.t_Transcript) u8)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                      t13.Tls13formats.t_Transcript) u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t13.Tls13formats.t_Transcript) u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t13.Tls13formats.t_Transcript) u8))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
              t13.Tls13formats.t_Transcript) u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
              t13.Tls13formats.t_Transcript) u8))
  | false, Core.Option.Option_None , Rust_primitives.Integers.MkInt 0 ->
    let tx_ch:t13.Tls13formats.t_Transcript = t13.Tls13formats.impl_Transcript__add tx ch in
    ks,
    (Core.Result.Result_Ok
      (ch,
        (Core.Option.Option_None <: Core.Option.t_Option t13.Tls13record.t_ClientCipherState0),
        tx_ch
        <:
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
          t13.Tls13formats.t_Transcript))
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
          t13.Tls13formats.t_Transcript) u8)
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
          t13.Tls13formats.t_Transcript) u8)
  | _ ->
    ks,
    (Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
          t13.Tls13formats.t_Transcript) u8)
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
          t13.Tls13formats.t_Transcript) u8)

let build_client_hello
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (sn: t13.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tx:t13.Tls13formats.t_Transcript =
    t13.Tls13formats.impl_Transcript__new (t13.Tls13crypto.impl_Algorithms__hash ciphersuite
        <:
        t13.Tls13crypto.t_HashAlgorithm)
  in
  let client_random:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let tmp0, tmp1:(iimpl_447424039_ & t_Array u8 (mk_usize 32)) =
    Rand_core.f_fill_bytes #iimpl_447424039_ #FStar.Tactics.Typeclasses.solve rng client_random
  in
  let rng:iimpl_447424039_ = tmp0 in
  let client_random:t_Array u8 (mk_usize 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, out:(iimpl_447424039_ &
    Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes) u8) =
    t13.Tls13crypto.kem_keygen #iimpl_447424039_
      (t13.Tls13crypto.impl_Algorithms__kem ciphersuite <: t13.Tls13crypto.t_KemScheme)
      rng
  in
  let rng:iimpl_447424039_ = tmp0 in
  match out <: Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes) u8 with
  | Core.Result.Result_Ok (kem_sk, kem_pk) ->
    (match
        t13.Tls13formats.client_hello ciphersuite
          (t13.Tls13utils.bytes (client_random <: t_Slice u8) <: t13.Tls13utils.t_Bytes)
          kem_pk
          sn
          tkt
        <:
        Core.Result.t_Result (t13.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
      with
      | Core.Result.Result_Ok (client_hello, trunc_len) ->
        let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
              t13.Tls13formats.t_Transcript) u8) =
          compute_psk_binder_zero_rtt ciphersuite client_hello trunc_len psk tx ks
        in
        let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
        (match
            out
            <:
            Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                t13.Tls13formats.t_Transcript) u8
          with
          | Core.Result.Result_Ok (nch, cipher0, tx_ch) ->
            let hax_temp_output:Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                t_ClientPostClientHello) u8 =
              Core.Result.Result_Ok
              (nch,
                cipher0,
                (ClientPostClientHello
                    (Core.Convert.f_into #(t_Array u8 (mk_usize 32))
                        #t13.Tls13utils.t_Bytes
                        #FStar.Tactics.Typeclasses.solve
                        client_random) ciphersuite kem_sk psk tx_ch
                  <:
                  t_ClientPostClientHello)
                <:
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello))
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8
            in
            rng, ks, hax_temp_output
            <:
            (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
          | Core.Result.Result_Err err ->
            rng,
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            <:
            (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8))
      | Core.Result.Result_Err err ->
        rng,
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8)
        <:
        (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8))
  | Core.Result.Result_Err err ->
    rng,
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
          t_ClientPostClientHello) u8)
    <:
    (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
          t_ClientPostClientHello) u8)

let put_server_hello
      (handshake: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (state: t_ClientPostClientHello)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let ClientPostClientHello client_random ciphersuite sk psk tx:t_ClientPostClientHello = state in
  match
    t13.Tls13formats.parse_server_hello ciphersuite handshake
    <:
    Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes) u8
  with
  | Core.Result.Result_Ok (sr, ct) ->
    let tx:t13.Tls13formats.t_Transcript =
      t13.Tls13formats.impl_Transcript__add tx handshake
    in
    (match
        t13.Tls13crypto.kem_decap ciphersuite.t13.Tls13crypto.f_kem ct sk
        <:
        Core.Result.t_Result t13.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok shared_secret ->
        (match
            t13.Tls13formats.impl_Transcript__transcript_hash tx
            <:
            Core.Result.t_Result t13.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok th ->
            let shared_secret_handle:t13.Tls13keyscheduler.Key_schedule.t_Handle =
              {
                t13.Tls13keyscheduler.Key_schedule.f_name
                =
                t13.Tls13keyscheduler.Key_schedule.TLSnames_KEM
                <:
                t13.Tls13keyscheduler.Key_schedule.t_TLSnames;
                t13.Tls13keyscheduler.Key_schedule.f_alg = ciphersuite.t13.Tls13crypto.f_hash;
                t13.Tls13keyscheduler.Key_schedule.f_level = mk_u8 0
              }
              <:
              t13.Tls13keyscheduler.Key_schedule.t_Handle
            in
            let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler =
              t13.Tls13keyscheduler.Key_schedule.set_by_handle ks
                shared_secret_handle
                shared_secret
            in
            let ks, psk_handle:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Option.t_Option t13.Tls13keyscheduler.Key_schedule.t_Handle) =
              match psk <: Core.Option.t_Option t13.Tls13utils.t_Bytes with
              | Core.Option.Option_Some bytes ->
                let handle:t13.Tls13keyscheduler.Key_schedule.t_Handle =
                  {
                    t13.Tls13keyscheduler.Key_schedule.f_name
                    =
                    t13.Tls13keyscheduler.Key_schedule.TLSnames_PSK
                    <:
                    t13.Tls13keyscheduler.Key_schedule.t_TLSnames;
                    t13.Tls13keyscheduler.Key_schedule.f_alg
                    =
                    ciphersuite.t13.Tls13crypto.f_hash;
                    t13.Tls13keyscheduler.Key_schedule.f_level = mk_u8 0
                  }
                  <:
                  t13.Tls13keyscheduler.Key_schedule.t_Handle
                in
                let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler =
                  t13.Tls13keyscheduler.Key_schedule.set_by_handle ks handle bytes
                in
                ks,
                (Core.Option.Option_Some handle
                  <:
                  Core.Option.t_Option t13.Tls13keyscheduler.Key_schedule.t_Handle)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Option.t_Option t13.Tls13keyscheduler.Key_schedule.t_Handle)
              | Core.Option.Option_None  ->
                ks,
                (Core.Option.Option_None
                  <:
                  Core.Option.t_Option t13.Tls13keyscheduler.Key_schedule.t_Handle)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Option.t_Option t13.Tls13keyscheduler.Key_schedule.t_Handle)
            in
            let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13keyscheduler.Key_schedule.t_Handle &
                  t13.Tls13keyscheduler.Key_schedule.t_Handle &
                  t13.Tls13keyscheduler.Key_schedule.t_Handle) u8) =
              t13.Tls13keyscheduler.derive_hk_handles ciphersuite.t13.Tls13crypto.f_hash
                shared_secret_handle
                psk_handle
                th
                ks
            in
            let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
            (match
                out
                <:
                Core.Result.t_Result
                  (t13.Tls13keyscheduler.Key_schedule.t_Handle &
                    t13.Tls13keyscheduler.Key_schedule.t_Handle &
                    t13.Tls13keyscheduler.Key_schedule.t_Handle) u8
              with
              | Core.Result.Result_Ok (ch_handle, sh_handle, ms_handle) ->
                let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                      t13.Tls13utils.t_Bytes &
                      t13.Tls13utils.t_Bytes) u8) =
                  t13.Tls13keyscheduler.derive_hk_ms ciphersuite.t13.Tls13crypto.f_hash
                    ciphersuite.t13.Tls13crypto.f_aead
                    ch_handle
                    sh_handle
                    ks
                in
                let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                (match
                    out
                    <:
                    Core.Result.t_Result
                      (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                        t13.Tls13utils.t_Bytes &
                        t13.Tls13utils.t_Bytes) u8
                  with
                  | Core.Result.Result_Ok (chk, shk, cfk, sfk) ->
                    let hax_temp_output:Core.Result.t_Result
                      (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8 =
                      Core.Result.Result_Ok
                      (t13.Tls13record.impl_DuplexCipherStateH__new chk (mk_u64 0) shk (mk_u64 0),
                        (ClientPostServerHello client_random sr ciphersuite ms_handle cfk sfk tx
                          <:
                          t_ClientPostServerHello)
                        <:
                        (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello))
                      <:
                      Core.Result.t_Result
                        (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8
                    in
                    ks, hax_temp_output
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
                  | Core.Result.Result_Err err ->
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8))
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello)
            u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello)
            u8))
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)

let put_server_signature
      (encrypted_extensions server_certificate server_certificate_verify:
          t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
     =
  let
  ClientPostServerHello
    client_random
    server_random
    algorithms
    master_secret_handle
    client_finished_key
    server_finished_key
    transcript:t_ClientPostServerHello =
    handshake_state
  in
  if ~.(t13.Tls13crypto.impl_Algorithms__psk_mode algorithms <: bool)
  then
    match
      t13.Tls13formats.parse_encrypted_extensions algorithms encrypted_extensions
      <:
      Core.Result.t_Result Prims.unit u8
    with
    | Core.Result.Result_Ok _ ->
      let transcript:t13.Tls13formats.t_Transcript =
        t13.Tls13formats.impl_Transcript__add transcript encrypted_extensions
      in
      (match
          t13.Tls13formats.parse_server_certificate server_certificate
          <:
          Core.Result.t_Result t13.Tls13utils.t_Bytes u8
        with
        | Core.Result.Result_Ok certificate ->
          let transcript:t13.Tls13formats.t_Transcript =
            t13.Tls13formats.impl_Transcript__add transcript server_certificate
          in
          (match
              t13.Tls13formats.impl_Transcript__transcript_hash transcript
              <:
              Core.Result.t_Result t13.Tls13utils.t_Bytes u8
            with
            | Core.Result.Result_Ok transcript_hash_server_certificate ->
              (match
                  t13.Tls13cert.verification_key_from_cert certificate
                  <:
                  Core.Result.t_Result
                    (t13.Tls13crypto.t_SignatureScheme & t13.Tls13cert.t_CertificateKey) u8
                with
                | Core.Result.Result_Ok spki ->
                  (match
                      t13.Tls13cert.cert_public_key certificate spki
                      <:
                      Core.Result.t_Result t13.Tls13crypto.t_PublicVerificationKey u8
                    with
                    | Core.Result.Result_Ok cert_pk ->
                      (match
                          t13.Tls13formats.parse_certificate_verify algorithms
                            server_certificate_verify
                          <:
                          Core.Result.t_Result t13.Tls13utils.t_Bytes u8
                        with
                        | Core.Result.Result_Ok cert_signature ->
                          let sigval:t13.Tls13utils.t_Bytes =
                            t13.Tls13utils.impl_Bytes__concat (t13.Tls13utils.impl_Bytes__from_slice
                                  (t13.Tls13formats.v_PREFIX_SERVER_SIGNATURE <: t_Slice u8)
                                <:
                                t13.Tls13utils.t_Bytes)
                              transcript_hash_server_certificate
                          in
                          (match
                              t13.Tls13crypto.verify (t13.Tls13crypto.impl_Algorithms__signature
                                    algorithms
                                  <:
                                  t13.Tls13crypto.t_SignatureScheme)
                                cert_pk
                                sigval
                                cert_signature
                              <:
                              Core.Result.t_Result Prims.unit u8
                            with
                            | Core.Result.Result_Ok _ ->
                              let transcript:t13.Tls13formats.t_Transcript =
                                t13.Tls13formats.impl_Transcript__add transcript
                                  server_certificate_verify
                              in
                              Core.Result.Result_Ok
                              (ClientPostCertificateVerify client_random
                                  server_random
                                  algorithms
                                  master_secret_handle
                                  client_finished_key
                                  server_finished_key
                                  transcript
                                <:
                                t_ClientPostCertificateVerify)
                              <:
                              Core.Result.t_Result t_ClientPostCertificateVerify u8
                            | Core.Result.Result_Err err ->
                              Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result t_ClientPostCertificateVerify u8)
                        | Core.Result.Result_Err err ->
                          Core.Result.Result_Err err
                          <:
                          Core.Result.t_Result t_ClientPostCertificateVerify u8)
                    | Core.Result.Result_Err err ->
                      Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result t_ClientPostCertificateVerify u8)
                | Core.Result.Result_Err err ->
                  Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result t_ClientPostCertificateVerify u8)
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result t_ClientPostCertificateVerify u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result t_ClientPostCertificateVerify u8
  else
    Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result t_ClientPostCertificateVerify u8

let put_psk_skip_server_signature
      (encrypted_extensions: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
     =
  let
  ClientPostServerHello
    client_random
    server_random
    algorithms
    master_secret_handle
    client_finished_key
    server_finished_key
    transcript:t_ClientPostServerHello =
    handshake_state
  in
  if t13.Tls13crypto.impl_Algorithms__psk_mode algorithms
  then
    match
      t13.Tls13formats.parse_encrypted_extensions algorithms encrypted_extensions
      <:
      Core.Result.t_Result Prims.unit u8
    with
    | Core.Result.Result_Ok _ ->
      let transcript:t13.Tls13formats.t_Transcript =
        t13.Tls13formats.impl_Transcript__add transcript encrypted_extensions
      in
      Core.Result.Result_Ok
      (ClientPostCertificateVerify client_random
          server_random
          algorithms
          master_secret_handle
          client_finished_key
          server_finished_key
          transcript
        <:
        t_ClientPostCertificateVerify)
      <:
      Core.Result.t_Result t_ClientPostCertificateVerify u8
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result t_ClientPostCertificateVerify u8
  else
    Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result t_ClientPostCertificateVerify u8

let put_server_finished
      (server_finished: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostCertificateVerify)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let
  ClientPostCertificateVerify
    client_random
    server_random
    algorithms
    master_secret_handle
    client_finished_key
    server_finished_key
    transcript:t_ClientPostCertificateVerify =
    handshake_state
  in
  let
  { t13.Tls13crypto.f_hash = hash ;
    t13.Tls13crypto.f_aead = aead ;
    t13.Tls13crypto.f_signature = signature ;
    t13.Tls13crypto.f_kem = kem ;
    t13.Tls13crypto.f_psk_mode = psk_mode ;
    t13.Tls13crypto.f_zero_rtt = zero_rtt }:t13.Tls13crypto.t_Algorithms =
    algorithms
  in
  match
    t13.Tls13formats.impl_Transcript__transcript_hash transcript
    <:
    Core.Result.t_Result t13.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok transcript_hash ->
    (match
        t13.Tls13formats.parse_finished server_finished
        <:
        Core.Result.t_Result t13.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok verify_data ->
        (match
            t13.Tls13crypto.hmac_verify hash server_finished_key transcript_hash verify_data
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            let transcript:t13.Tls13formats.t_Transcript =
              t13.Tls13formats.impl_Transcript__add transcript server_finished
            in
            (match
                t13.Tls13formats.impl_Transcript__transcript_hash transcript
                <:
                Core.Result.t_Result t13.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok transcript_hash_server_finished ->
                let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13keyscheduler.Key_schedule.t_Handle &
                      t13.Tls13keyscheduler.Key_schedule.t_Handle &
                      t13.Tls13keyscheduler.Key_schedule.t_Handle) u8) =
                  t13.Tls13keyscheduler.derive_app_handles hash
                    master_secret_handle
                    transcript_hash_server_finished
                    ks
                in
                let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                (match
                    out
                    <:
                    Core.Result.t_Result
                      (t13.Tls13keyscheduler.Key_schedule.t_Handle &
                        t13.Tls13keyscheduler.Key_schedule.t_Handle &
                        t13.Tls13keyscheduler.Key_schedule.t_Handle) u8
                  with
                  | Core.Result.Result_Ok (ca_handle, sa_handle, exp_handle) ->
                    let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV) u8) =
                      t13.Tls13keyscheduler.derive_app_keys hash aead ca_handle sa_handle ks
                    in
                    let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                    (match
                        out
                        <:
                        Core.Result.t_Result
                          (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV) u8
                      with
                      | Core.Result.Result_Ok (cak, sak) ->
                        (match
                            t13.Tls13keyscheduler.Key_schedule.tagkey_from_handle ks exp_handle
                            <:
                            Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_TagKey u8
                          with
                          | Core.Result.Result_Ok exp ->
                            let cipher1:t13.Tls13record.t_DuplexCipherState1 =
                              t13.Tls13record.duplex_cipher_state1 aead
                                cak
                                (mk_u64 0)
                                sak
                                (mk_u64 0)
                                exp
                            in
                            let hax_temp_output:Core.Result.t_Result
                              (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
                              u8 =
                              Core.Result.Result_Ok
                              (cipher1,
                                (ClientPostServerFinished client_random
                                    server_random
                                    algorithms
                                    master_secret_handle
                                    client_finished_key
                                    transcript
                                  <:
                                  t_ClientPostServerFinished)
                                <:
                                (t13.Tls13record.t_DuplexCipherState1 &
                                  t_ClientPostServerFinished))
                              <:
                              Core.Result.t_Result
                                (t13.Tls13record.t_DuplexCipherState1 &
                                  t_ClientPostServerFinished) u8
                            in
                            ks, hax_temp_output
                            <:
                            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                              Core.Result.t_Result
                                (t13.Tls13record.t_DuplexCipherState1 &
                                  t_ClientPostServerFinished) u8)
                          | Core.Result.Result_Err err ->
                            ks,
                            (Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result
                                (t13.Tls13record.t_DuplexCipherState1 &
                                  t_ClientPostServerFinished) u8)
                            <:
                            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                              Core.Result.t_Result
                                (t13.Tls13record.t_DuplexCipherState1 &
                                  t_ClientPostServerFinished) u8))
                      | Core.Result.Result_Err err ->
                        ks,
                        (Core.Result.Result_Err err
                          <:
                          Core.Result.t_Result
                            (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
                            u8)
                        <:
                        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                          Core.Result.t_Result
                            (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
                            u8))
                  | Core.Result.Result_Err err ->
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8))
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8))
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8
    )
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8
    )

let get_client_finished
      (handshake_state: t_ClientPostServerFinished)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let
  ClientPostServerFinished
    client_random
    server_random
    algorithms
    master_secret_handle
    client_finished_key
    transcript:t_ClientPostServerFinished =
    handshake_state
  in
  match
    t13.Tls13formats.impl_Transcript__transcript_hash transcript
    <:
    Core.Result.t_Result t13.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok transcript_hash ->
    (match
        t13.Tls13crypto.hmac_tag (t13.Tls13crypto.impl_Algorithms__hash algorithms
            <:
            t13.Tls13crypto.t_HashAlgorithm)
          client_finished_key
          transcript_hash
        <:
        Core.Result.t_Result t13.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok verify_data ->
        (match
            t13.Tls13formats.finished verify_data
            <:
            Core.Result.t_Result t13.Tls13formats.Handshake_data.t_HandshakeData u8
          with
          | Core.Result.Result_Ok client_finished ->
            let transcript:t13.Tls13formats.t_Transcript =
              t13.Tls13formats.impl_Transcript__add transcript client_finished
            in
            (match
                t13.Tls13formats.impl_Transcript__transcript_hash transcript
                <:
                Core.Result.t_Result t13.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok transcript_hash ->
                let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8) =
                  t13.Tls13keyscheduler.derive_rms (t13.Tls13crypto.impl_Algorithms__hash algorithms

                      <:
                      t13.Tls13crypto.t_HashAlgorithm)
                    master_secret_handle
                    transcript_hash
                    ks
                in
                let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                (match
                    out <: Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8
                  with
                  | Core.Result.Result_Ok resumption_master_secret ->
                    let hax_temp_output:Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t_ClientPostClientFinished) u8 =
                      Core.Result.Result_Ok
                      (client_finished,
                        (ClientPostClientFinished client_random
                            server_random
                            algorithms
                            resumption_master_secret
                            transcript
                          <:
                          t_ClientPostClientFinished)
                        <:
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ClientPostClientFinished))
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ClientPostClientFinished) u8
                    in
                    ks, hax_temp_output
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ClientPostClientFinished) u8)
                  | Core.Result.Result_Err err ->
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ClientPostClientFinished) u8)
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ClientPostClientFinished) u8))
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished
                    ) u8)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished
                    ) u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8
            )
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8
            ))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8))
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8)
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8)

let client_init
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (algs: t13.Tls13crypto.t_Algorithms)
      (sn: t13.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, tmp1, out:(iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8) =
    build_client_hello #iimpl_447424039_ algs sn tkt psk rng ks
  in
  let rng:iimpl_447424039_ = tmp0 in
  let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp1 in
  let hax_temp_output:Core.Result.t_Result
    (t13.Tls13formats.Handshake_data.t_HandshakeData &
      Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
      t_ClientPostClientHello) u8 =
    out
  in
  rng, ks, hax_temp_output
  <:
  (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8)

let client_set_params
      (payload: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ClientPostClientHello)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8) =
    put_server_hello payload st ks
  in
  let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  let hax_temp_output:Core.Result.t_Result
    (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8 =
    out
  in
  ks, hax_temp_output
  <:
  (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)

let client_finish
      (payload: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  match
    t13.Tls13crypto.impl_Algorithms__psk_mode (algs_post_server_hello handshake_state
        <:
        t13.Tls13crypto.t_Algorithms)
    <:
    bool
  with
  | false ->
    (match
        t13.Tls13formats.Handshake_data.impl_HandshakeData__to_four payload
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData) u8
      with
      | Core.Result.Result_Ok
        (encrypted_extensions, server_certificate, server_certificate_verify, server_finished) ->
        (match
            put_server_signature encrypted_extensions
              server_certificate
              server_certificate_verify
              handshake_state
            <:
            Core.Result.t_Result t_ClientPostCertificateVerify u8
          with
          | Core.Result.Result_Ok client_state_certificate_verify ->
            let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8) =
              put_server_finished server_finished client_state_certificate_verify ks
            in
            let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
            (match
                out
                <:
                Core.Result.t_Result
                  (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8
              with
              | Core.Result.Result_Ok (cipher, client_state_server_finished) ->
                let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished
                    ) u8) =
                  get_client_finished client_state_server_finished ks
                in
                let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                (match
                    out
                    <:
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t_ClientPostClientFinished) u8
                  with
                  | Core.Result.Result_Ok (client_finished, client_state) ->
                    ks,
                    (Core.Result.Result_Ok
                      (client_finished, cipher, client_state
                        <:
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherState1 &
                          t_ClientPostClientFinished))
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherState1 &
                          t_ClientPostClientFinished) u8)
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherState1 &
                          t_ClientPostClientFinished) u8)
                  | Core.Result.Result_Err err ->
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherState1 &
                          t_ClientPostClientFinished) u8)
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherState1 &
                          t_ClientPostClientFinished) u8))
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ClientPostClientFinished) u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ClientPostClientFinished) u8))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished) u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished) u8))
  | true ->
    match
      t13.Tls13formats.Handshake_data.impl_HandshakeData__to_two payload
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData) u8
    with
    | Core.Result.Result_Ok (encrypted_extensions, server_finished) ->
      (match
          put_psk_skip_server_signature encrypted_extensions handshake_state
          <:
          Core.Result.t_Result t_ClientPostCertificateVerify u8
        with
        | Core.Result.Result_Ok client_state_certificate_verify ->
          let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
            Core.Result.t_Result
              (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8) =
            put_server_finished server_finished client_state_certificate_verify ks
          in
          let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
          (match
              out
              <:
              Core.Result.t_Result
                (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8
            with
            | Core.Result.Result_Ok (cipher, client_state_server_finished) ->
              let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished)
                  u8) =
                get_client_finished client_state_server_finished ks
              in
              let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
              (match
                  out
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished
                    ) u8
                with
                | Core.Result.Result_Ok (client_finished, client_state) ->
                  ks,
                  (Core.Result.Result_Ok
                    (client_finished, cipher, client_state
                      <:
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherState1 &
                        t_ClientPostClientFinished))
                    <:
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherState1 &
                        t_ClientPostClientFinished) u8)
                  <:
                  (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherState1 &
                        t_ClientPostClientFinished) u8)
                | Core.Result.Result_Err err ->
                  ks,
                  (Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherState1 &
                        t_ClientPostClientFinished) u8)
                  <:
                  (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherState1 &
                        t_ClientPostClientFinished) u8))
            | Core.Result.Result_Err err ->
              ks,
              (Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    t13.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              <:
              (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    t13.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8))
        | Core.Result.Result_Err err ->
          ks,
          (Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                t13.Tls13record.t_DuplexCipherState1 &
                t_ClientPostClientFinished) u8)
          <:
          (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
            Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                t13.Tls13record.t_DuplexCipherState1 &
                t_ClientPostClientFinished) u8))
    | Core.Result.Result_Err err ->
      ks,
      (Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ClientPostClientFinished) u8)
      <:
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ClientPostClientFinished) u8)

let process_psk_binder_zero_rtt
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (th_trunc th: t13.Tls13utils.t_Bytes)
      (psko bindero: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  match
    ciphersuite.t13.Tls13crypto.f_psk_mode, psko, bindero
    <:
    (bool & Core.Option.t_Option t13.Tls13utils.t_Bytes &
      Core.Option.t_Option t13.Tls13utils.t_Bytes)
  with
  | true, Core.Option.Option_Some k, Core.Option.Option_Some binder ->
    let psk_handle:t13.Tls13keyscheduler.Key_schedule.t_Handle =
      {
        t13.Tls13keyscheduler.Key_schedule.f_name
        =
        t13.Tls13keyscheduler.Key_schedule.TLSnames_PSK
        <:
        t13.Tls13keyscheduler.Key_schedule.t_TLSnames;
        t13.Tls13keyscheduler.Key_schedule.f_alg = ciphersuite.t13.Tls13crypto.f_hash;
        t13.Tls13keyscheduler.Key_schedule.f_level = mk_u8 0
      }
      <:
      t13.Tls13keyscheduler.Key_schedule.t_Handle
    in
    let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler =
      t13.Tls13keyscheduler.Key_schedule.set_by_handle ks
        psk_handle
        (Core.Clone.f_clone #t13.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve k
          <:
          t13.Tls13utils.t_Bytes)
    in
    let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8) =
      t13.Tls13keyscheduler.derive_binder_key ciphersuite.t13.Tls13crypto.f_hash psk_handle ks
    in
    let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
    (match out <: Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8 with
      | Core.Result.Result_Ok mk_handle ->
        (match
            t13.Tls13keyscheduler.Key_schedule.tagkey_from_handle ks mk_handle
            <:
            Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_TagKey u8
          with
          | Core.Result.Result_Ok hoist111 ->
            let mk:t13.Tls13utils.t_Bytes =
              hoist111.t13.Tls13keyscheduler.Key_schedule.f_val
            in
            let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8) =
              t13.Tls13keyscheduler.Key_schedule.v_XPD ks
                (t13.Tls13keyscheduler.Key_schedule.TLSnames_Binder
                  <:
                  t13.Tls13keyscheduler.Key_schedule.t_TLSnames)
                (mk_u8 0)
                mk_handle
                true
                th_trunc
            in
            let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
            (match
                out <: Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8
              with
              | Core.Result.Result_Ok binder_handle ->
                (match
                    t13.Tls13keyscheduler.Key_schedule.tagkey_from_handle ks binder_handle
                    <:
                    Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_TagKey u8
                  with
                  | Core.Result.Result_Ok hoist113 ->
                    let binder:t13.Tls13utils.t_Bytes =
                      hoist113.t13.Tls13keyscheduler.Key_schedule.f_val
                    in
                    (match
                        t13.Tls13crypto.hmac_verify ciphersuite.t13.Tls13crypto.f_hash
                          mk
                          th_trunc
                          binder
                        <:
                        Core.Result.t_Result Prims.unit u8
                      with
                      | Core.Result.Result_Ok _ ->
                        if ciphersuite.t13.Tls13crypto.f_zero_rtt
                        then
                          let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                            Core.Result.t_Result
                              (t13.Tls13crypto.t_AeadKeyIV &
                                t13.Tls13keyscheduler.Key_schedule.t_Handle) u8) =
                            t13.Tls13keyscheduler.derive_0rtt_keys ciphersuite
                                .t13.Tls13crypto.f_hash
                              ciphersuite.t13.Tls13crypto.f_aead
                              psk_handle
                              th
                              ks
                          in
                          let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                          match
                            out
                            <:
                            Core.Result.t_Result
                              (t13.Tls13crypto.t_AeadKeyIV &
                                t13.Tls13keyscheduler.Key_schedule.t_Handle) u8
                          with
                          | Core.Result.Result_Ok (key_iv, early_exporter_ms_handle) ->
                            (match
                                t13.Tls13keyscheduler.Key_schedule.tagkey_from_handle ks
                                  early_exporter_ms_handle
                                <:
                                Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_TagKey
                                  u8
                              with
                              | Core.Result.Result_Ok early_exporter_ms ->
                                ks,
                                (Core.Result.Result_Ok
                                  (Core.Option.Option_Some
                                    (t13.Tls13record.server_cipher_state0 key_iv
                                        (mk_u64 0)
                                        early_exporter_ms)
                                    <:
                                    Core.Option.t_Option t13.Tls13record.t_ServerCipherState0)
                                  <:
                                  Core.Result.t_Result
                                    (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0)
                                    u8)
                                <:
                                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                                  Core.Result.t_Result
                                    (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0)
                                    u8)
                              | Core.Result.Result_Err err ->
                                ks,
                                (Core.Result.Result_Err err
                                  <:
                                  Core.Result.t_Result
                                    (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0)
                                    u8)
                                <:
                                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                                  Core.Result.t_Result
                                    (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0)
                                    u8))
                          | Core.Result.Result_Err err ->
                            ks,
                            (Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result
                                (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
                            <:
                            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                              Core.Result.t_Result
                                (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
                        else
                          ks,
                          (Core.Result.Result_Ok
                            (Core.Option.Option_None
                              <:
                              Core.Option.t_Option t13.Tls13record.t_ServerCipherState0)
                            <:
                            Core.Result.t_Result
                              (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
                          <:
                          (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                            Core.Result.t_Result
                              (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
                      | Core.Result.Result_Err err ->
                        ks,
                        (Core.Result.Result_Err err
                          <:
                          Core.Result.t_Result
                            (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
                        <:
                        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                          Core.Result.t_Result
                            (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8))
                  | Core.Result.Result_Err err ->
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8))
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8
            )
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8
            ))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8))
  | false, Core.Option.Option_None , Core.Option.Option_None  ->
    ks,
    (Core.Result.Result_Ok
      (Core.Option.Option_None <: Core.Option.t_Option t13.Tls13record.t_ServerCipherState0)
      <:
      Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
  | _ ->
    ks,
    (Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
      <:
      Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)

let put_client_hello
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  match
    t13.Tls13formats.parse_client_hello ciphersuite ch
    <:
    Core.Result.t_Result
      (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes &
        t13.Tls13utils.t_Bytes &
        Core.Option.t_Option t13.Tls13utils.t_Bytes &
        Core.Option.t_Option t13.Tls13utils.t_Bytes &
        usize) u8
  with
  | Core.Result.Result_Ok (client_randomness, session_id, sni, gx, tkto, bindero, trunc_len) ->
    let tx:t13.Tls13formats.t_Transcript =
      t13.Tls13formats.impl_Transcript__new (t13.Tls13crypto.impl_Algorithms__hash ciphersuite
          <:
          t13.Tls13crypto.t_HashAlgorithm)
    in
    (match
        t13.Tls13formats.impl_Transcript__transcript_hash_without_client_hello tx ch trunc_len
        <:
        Core.Result.t_Result t13.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok th_trunc ->
        let transcript:t13.Tls13formats.t_Transcript =
          t13.Tls13formats.impl_Transcript__add tx ch
        in
        (match
            t13.Tls13formats.impl_Transcript__transcript_hash transcript
            <:
            Core.Result.t_Result t13.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok th ->
            (match
                t13.Server.lookup_db ciphersuite db sni tkto
                <:
                Core.Result.t_Result t13.Server.t_ServerInfo u8
              with
              | Core.Result.Result_Ok server ->
                let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8) =
                  process_psk_binder_zero_rtt ciphersuite
                    th_trunc
                    th
                    server.t13.Server.f_psk_opt
                    bindero
                    ks
                in
                let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                (match
                    out
                    <:
                    Core.Result.t_Result
                      (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8
                  with
                  | Core.Result.Result_Ok cipher0 ->
                    let hax_temp_output:Core.Result.t_Result
                      (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                        t_ServerPostClientHello) u8 =
                      Core.Result.Result_Ok
                      (cipher0,
                        ({
                            f_client_randomness = client_randomness;
                            f_ciphersuite = ciphersuite;
                            f_session_id = session_id;
                            f_gx = gx;
                            f_server = server;
                            f_transcript = transcript
                          }
                          <:
                          t_ServerPostClientHello)
                        <:
                        (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                          t_ServerPostClientHello))
                      <:
                      Core.Result.t_Result
                        (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                          t_ServerPostClientHello) u8
                    in
                    ks, hax_temp_output
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                          t_ServerPostClientHello) u8)
                  | Core.Result.Result_Err err ->
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                          t_ServerPostClientHello) u8)
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                          t_ServerPostClientHello) u8))
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t_ServerPostClientHello) u8)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t_ServerPostClientHello) u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
            u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
            u8))
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8)
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8)

let get_server_hello
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (state: t_ServerPostClientHello)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let server_random:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let tmp0, tmp1:(iimpl_447424039_ & t_Array u8 (mk_usize 32)) =
    Rand_core.f_fill_bytes #iimpl_447424039_ #FStar.Tactics.Typeclasses.solve rng server_random
  in
  let rng:iimpl_447424039_ = tmp0 in
  let server_random:t_Array u8 (mk_usize 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, out:(iimpl_447424039_ &
    Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes) u8) =
    t13.Tls13crypto.kem_encap #iimpl_447424039_
      state.f_ciphersuite.t13.Tls13crypto.f_kem
      state.f_gx
      rng
  in
  let rng:iimpl_447424039_ = tmp0 in
  match out <: Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes) u8 with
  | Core.Result.Result_Ok (shared_secret, gy) ->
    let shared_secret_handle:t13.Tls13keyscheduler.Key_schedule.t_Handle =
      {
        t13.Tls13keyscheduler.Key_schedule.f_name
        =
        t13.Tls13keyscheduler.Key_schedule.TLSnames_KEM
        <:
        t13.Tls13keyscheduler.Key_schedule.t_TLSnames;
        t13.Tls13keyscheduler.Key_schedule.f_alg = state.f_ciphersuite.t13.Tls13crypto.f_hash;
        t13.Tls13keyscheduler.Key_schedule.f_level = mk_u8 0
      }
      <:
      t13.Tls13keyscheduler.Key_schedule.t_Handle
    in
    let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler =
      t13.Tls13keyscheduler.Key_schedule.set_by_handle ks shared_secret_handle shared_secret
    in
    (match
        t13.Tls13formats.server_hello state.f_ciphersuite
          (t13.Tls13utils.bytes (server_random <: t_Slice u8) <: t13.Tls13utils.t_Bytes)
          state.f_session_id
          gy
        <:
        Core.Result.t_Result t13.Tls13formats.Handshake_data.t_HandshakeData u8
      with
      | Core.Result.Result_Ok sh ->
        let transcript:t13.Tls13formats.t_Transcript =
          t13.Tls13formats.impl_Transcript__add state.f_transcript sh
        in
        (match
            t13.Tls13formats.impl_Transcript__transcript_hash transcript
            <:
            Core.Result.t_Result t13.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok transcript_hash ->
            let psk_handle:Core.Option.t_Option t13.Tls13utils.t_Bytes =
              Core.Clone.f_clone #(Core.Option.t_Option t13.Tls13utils.t_Bytes)
                #FStar.Tactics.Typeclasses.solve
                state.f_server.t13.Server.f_psk_opt
            in
            let ks, psk_handle:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Option.t_Option t13.Tls13keyscheduler.Key_schedule.t_Handle) =
              match psk_handle <: Core.Option.t_Option t13.Tls13utils.t_Bytes with
              | Core.Option.Option_Some bytes ->
                let handle:t13.Tls13keyscheduler.Key_schedule.t_Handle =
                  {
                    t13.Tls13keyscheduler.Key_schedule.f_name
                    =
                    t13.Tls13keyscheduler.Key_schedule.TLSnames_PSK
                    <:
                    t13.Tls13keyscheduler.Key_schedule.t_TLSnames;
                    t13.Tls13keyscheduler.Key_schedule.f_alg
                    =
                    state.f_ciphersuite.t13.Tls13crypto.f_hash;
                    t13.Tls13keyscheduler.Key_schedule.f_level = mk_u8 0
                  }
                  <:
                  t13.Tls13keyscheduler.Key_schedule.t_Handle
                in
                let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler =
                  t13.Tls13keyscheduler.Key_schedule.set_by_handle ks handle bytes
                in
                ks,
                (Core.Option.Option_Some handle
                  <:
                  Core.Option.t_Option t13.Tls13keyscheduler.Key_schedule.t_Handle)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Option.t_Option t13.Tls13keyscheduler.Key_schedule.t_Handle)
              | Core.Option.Option_None  ->
                ks,
                (Core.Option.Option_None
                  <:
                  Core.Option.t_Option t13.Tls13keyscheduler.Key_schedule.t_Handle)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Option.t_Option t13.Tls13keyscheduler.Key_schedule.t_Handle)
            in
            let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13keyscheduler.Key_schedule.t_Handle &
                  t13.Tls13keyscheduler.Key_schedule.t_Handle &
                  t13.Tls13keyscheduler.Key_schedule.t_Handle) u8) =
              t13.Tls13keyscheduler.derive_hk_handles state.f_ciphersuite
                  .t13.Tls13crypto.f_hash
                shared_secret_handle
                psk_handle
                transcript_hash
                ks
            in
            let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
            (match
                out
                <:
                Core.Result.t_Result
                  (t13.Tls13keyscheduler.Key_schedule.t_Handle &
                    t13.Tls13keyscheduler.Key_schedule.t_Handle &
                    t13.Tls13keyscheduler.Key_schedule.t_Handle) u8
              with
              | Core.Result.Result_Ok (ch_handle, sh_handle, ms_handle) ->
                let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                      t13.Tls13utils.t_Bytes &
                      t13.Tls13utils.t_Bytes) u8) =
                  t13.Tls13keyscheduler.derive_hk_ms state.f_ciphersuite
                      .t13.Tls13crypto.f_hash
                    state.f_ciphersuite.t13.Tls13crypto.f_aead
                    ch_handle
                    sh_handle
                    ks
                in
                let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                (match
                    out
                    <:
                    Core.Result.t_Result
                      (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                        t13.Tls13utils.t_Bytes &
                        t13.Tls13utils.t_Bytes) u8
                  with
                  | Core.Result.Result_Ok (chk, shk, cfk, sfk) ->
                    let hax_temp_output:Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherStateH &
                        t_ServerPostServerHello) u8 =
                      Core.Result.Result_Ok
                      (sh,
                        t13.Tls13record.impl_DuplexCipherStateH__new shk
                          (mk_u64 0)
                          chk
                          (mk_u64 0),
                        ({
                            f_client_random = state.f_client_randomness;
                            f_server_random
                            =
                            Core.Convert.f_into #(t_Array u8 (mk_usize 32))
                              #t13.Tls13utils.t_Bytes
                              #FStar.Tactics.Typeclasses.solve
                              server_random;
                            f_ciphersuite = state.f_ciphersuite;
                            f_server = state.f_server;
                            f_master_secret = ms_handle;
                            f_cfk = cfk;
                            f_sfk = sfk;
                            f_transcript = transcript
                          }
                          <:
                          t_ServerPostServerHello)
                        <:
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherStateH &
                          t_ServerPostServerHello))
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherStateH &
                          t_ServerPostServerHello) u8
                    in
                    rng, ks, hax_temp_output
                    <:
                    (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherStateH &
                          t_ServerPostServerHello) u8)
                  | Core.Result.Result_Err err ->
                    rng,
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherStateH &
                          t_ServerPostServerHello) u8)
                    <:
                    (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherStateH &
                          t_ServerPostServerHello) u8))
              | Core.Result.Result_Err err ->
                rng,
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
                <:
                (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8))
          | Core.Result.Result_Err err ->
            rng,
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8)
            <:
            (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8))
      | Core.Result.Result_Err err ->
        rng,
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8)
        <:
        (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8))
  | Core.Result.Result_Err err ->
    rng,
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8)
    <:
    (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8)

let get_rsa_signature
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (cert sk sigval: t13.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
     =
  match
    t13.Tls13cert.verification_key_from_cert cert
    <:
    Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t13.Tls13cert.t_CertificateKey)
      u8
  with
  | Core.Result.Result_Ok (cert_scheme, cert_slice) ->
    (match
        t13.Tls13cert.rsa_public_key cert cert_slice
        <:
        Core.Result.t_Result t13.Tls13crypto.t_RsaVerificationKey u8
      with
      | Core.Result.Result_Ok pk ->
        let tmp0, out:(iimpl_447424039_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8) =
          t13.Tls13crypto.sign_rsa #iimpl_447424039_
            sk
            pk.t13.Tls13crypto.f_modulus
            pk.t13.Tls13crypto.f_exponent
            cert_scheme
            sigval
            rng
        in
        let rng:iimpl_447424039_ = tmp0 in
        let hax_temp_output:Core.Result.t_Result t13.Tls13utils.t_Bytes u8 = out in
        rng, hax_temp_output
        <:
        (iimpl_447424039_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        rng, (Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
        <:
        (iimpl_447424039_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8))
  | Core.Result.Result_Err err ->
    rng, (Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
    <:
    (iimpl_447424039_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)

let get_server_signature_no_psk
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (state: t_ServerPostServerHello)
      (rng: iimpl_447424039_)
     =
  match
    t13.Tls13formats.encrypted_extensions state.f_ciphersuite
    <:
    Core.Result.t_Result t13.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok ee ->
    let transcript:t13.Tls13formats.t_Transcript =
      t13.Tls13formats.impl_Transcript__add state.f_transcript ee
    in
    (match
        t13.Tls13formats.server_certificate state.f_ciphersuite
          state.f_server.t13.Server.f_cert
        <:
        Core.Result.t_Result t13.Tls13formats.Handshake_data.t_HandshakeData u8
      with
      | Core.Result.Result_Ok sc ->
        let transcript:t13.Tls13formats.t_Transcript =
          t13.Tls13formats.impl_Transcript__add transcript sc
        in
        (match
            t13.Tls13formats.impl_Transcript__transcript_hash transcript
            <:
            Core.Result.t_Result t13.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok transcript_hash ->
            let sigval:t13.Tls13utils.t_Bytes =
              t13.Tls13utils.impl_Bytes__concat (t13.Tls13utils.impl_Bytes__from_slice (t13.Tls13formats.v_PREFIX_SERVER_SIGNATURE
                      <:
                      t_Slice u8)
                  <:
                  t13.Tls13utils.t_Bytes)
                transcript_hash
            in
            let rng, hoist118:(iimpl_447424039_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
            =
              match
                t13.Tls13crypto.impl_Algorithms__signature state.f_ciphersuite
                <:
                t13.Tls13crypto.t_SignatureScheme
              with
              | t13.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
                let tmp0, out:(iimpl_447424039_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
                =
                  t13.Tls13crypto.sign #iimpl_447424039_
                    (t13.Tls13crypto.impl_Algorithms__signature state.f_ciphersuite
                      <:
                      t13.Tls13crypto.t_SignatureScheme)
                    state.f_server.t13.Server.f_sk
                    sigval
                    rng
                in
                let rng:iimpl_447424039_ = tmp0 in
                rng, out <: (iimpl_447424039_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
              | t13.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
                let tmp0, out:(iimpl_447424039_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
                =
                  get_rsa_signature #iimpl_447424039_
                    state.f_server.t13.Server.f_cert
                    state.f_server.t13.Server.f_sk
                    sigval
                    rng
                in
                let rng:iimpl_447424039_ = tmp0 in
                rng, out <: (iimpl_447424039_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
              | t13.Tls13crypto.SignatureScheme_ED25519  ->
                rng,
                (Core.Result.Result_Err t13.Tls13utils.v_UNSUPPORTED_ALGORITHM
                  <:
                  Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
                <:
                (iimpl_447424039_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
            in
            (match hoist118 <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8 with
              | Core.Result.Result_Ok sig ->
                (match
                    t13.Tls13formats.certificate_verify state.f_ciphersuite sig
                    <:
                    Core.Result.t_Result t13.Tls13formats.Handshake_data.t_HandshakeData u8
                  with
                  | Core.Result.Result_Ok scv ->
                    let transcript:t13.Tls13formats.t_Transcript =
                      t13.Tls13formats.impl_Transcript__add transcript scv
                    in
                    let hax_temp_output:Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t_ServerPostCertificateVerify) u8 =
                      Core.Result.Result_Ok
                      (ee,
                        sc,
                        scv,
                        (ServerPostCertificateVerify state.f_client_random
                            state.f_server_random
                            state.f_ciphersuite
                            state.f_master_secret
                            state.f_cfk
                            state.f_sfk
                            transcript
                          <:
                          t_ServerPostCertificateVerify)
                        <:
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify))
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8
                    in
                    rng, hax_temp_output
                    <:
                    (iimpl_447424039_ &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                  | Core.Result.Result_Err err ->
                    rng,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    <:
                    (iimpl_447424039_ &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8))
              | Core.Result.Result_Err err ->
                rng,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
                <:
                (iimpl_447424039_ &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8))
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            <:
            (iimpl_447424039_ &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8)
        <:
        (iimpl_447424039_ &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          t_ServerPostCertificateVerify) u8)
    <:
    (iimpl_447424039_ &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          t_ServerPostCertificateVerify) u8)

let get_server_signature
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (state: t_ServerPostServerHello)
      (rng: iimpl_447424039_)
     =
  let rng, hax_temp_output:(iimpl_447424039_ &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
        t_ServerPostCertificateVerify) u8) =
    if ~.(t13.Tls13crypto.impl_Algorithms__psk_mode state.f_ciphersuite <: bool)
    then
      let tmp0, out:(iimpl_447424039_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8) =
        get_server_signature_no_psk #iimpl_447424039_ state rng
      in
      let rng:iimpl_447424039_ = tmp0 in
      rng, out
      <:
      (iimpl_447424039_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8)
    else
      rng,
      (Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8)
      <:
      (iimpl_447424039_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8)
  in
  rng, hax_temp_output
  <:
  (iimpl_447424039_ &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
        t_ServerPostCertificateVerify) u8)

let get_skip_server_signature_no_psk (st: t_ServerPostServerHello) =
  let
  { f_client_random = cr ;
    f_server_random = sr ;
    f_ciphersuite = algs ;
    f_server = server ;
    f_master_secret = ms ;
    f_cfk = cfk ;
    f_sfk = sfk ;
    f_transcript = tx }:t_ServerPostServerHello =
    st
  in
  match
    t13.Tls13formats.encrypted_extensions algs
    <:
    Core.Result.t_Result t13.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok ee ->
    let tx:t13.Tls13formats.t_Transcript = t13.Tls13formats.impl_Transcript__add tx ee in
    Core.Result.Result_Ok
    (ee, (ServerPostCertificateVerify cr sr algs ms cfk sfk tx <: t_ServerPostCertificateVerify)
      <:
      (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify))
    <:
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8

let get_skip_server_signature (st: t_ServerPostServerHello) =
  let
  { f_client_random = cr ;
    f_server_random = sr ;
    f_ciphersuite = algs ;
    f_server = server ;
    f_master_secret = ms ;
    f_cfk = cfk ;
    f_sfk = sfk ;
    f_transcript = tx }:t_ServerPostServerHello =
    st
  in
  if t13.Tls13crypto.impl_Algorithms__psk_mode algs
  then get_skip_server_signature_no_psk st
  else
    Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8

let get_server_finished
      (st: t_ServerPostCertificateVerify)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let ServerPostCertificateVerify cr sr algs ms_handle cfk sfk tx:t_ServerPostCertificateVerify =
    st
  in
  let
  { t13.Tls13crypto.f_hash = ha ;
    t13.Tls13crypto.f_aead = ae ;
    t13.Tls13crypto.f_signature = e_sa ;
    t13.Tls13crypto.f_kem = e_gn ;
    t13.Tls13crypto.f_psk_mode = e_psk_mode ;
    t13.Tls13crypto.f_zero_rtt = e_zero_rtt }:t13.Tls13crypto.t_Algorithms =
    algs
  in
  match
    t13.Tls13formats.impl_Transcript__transcript_hash tx
    <:
    Core.Result.t_Result t13.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok th_scv ->
    (match
        t13.Tls13crypto.hmac_tag ha sfk th_scv
        <:
        Core.Result.t_Result t13.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok vd ->
        (match
            t13.Tls13formats.finished vd
            <:
            Core.Result.t_Result t13.Tls13formats.Handshake_data.t_HandshakeData u8
          with
          | Core.Result.Result_Ok sfin ->
            let tx:t13.Tls13formats.t_Transcript =
              t13.Tls13formats.impl_Transcript__add tx sfin
            in
            (match
                t13.Tls13formats.impl_Transcript__transcript_hash tx
                <:
                Core.Result.t_Result t13.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok th_sfin ->
                let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13keyscheduler.Key_schedule.t_Handle &
                      t13.Tls13keyscheduler.Key_schedule.t_Handle &
                      t13.Tls13keyscheduler.Key_schedule.t_Handle) u8) =
                  t13.Tls13keyscheduler.derive_app_handles ha ms_handle th_sfin ks
                in
                let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                (match
                    out
                    <:
                    Core.Result.t_Result
                      (t13.Tls13keyscheduler.Key_schedule.t_Handle &
                        t13.Tls13keyscheduler.Key_schedule.t_Handle &
                        t13.Tls13keyscheduler.Key_schedule.t_Handle) u8
                  with
                  | Core.Result.Result_Ok (ca_handle, sa_handle, exp_handle) ->
                    let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV) u8) =
                      t13.Tls13keyscheduler.derive_app_keys ha ae ca_handle sa_handle ks
                    in
                    let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                    (match
                        out
                        <:
                        Core.Result.t_Result
                          (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV) u8
                      with
                      | Core.Result.Result_Ok (cak, sak) ->
                        (match
                            t13.Tls13keyscheduler.Key_schedule.tagkey_from_handle ks exp_handle
                            <:
                            Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_TagKey u8
                          with
                          | Core.Result.Result_Ok exp ->
                            let cipher1:t13.Tls13record.t_DuplexCipherState1 =
                              t13.Tls13record.duplex_cipher_state1 ae
                                sak
                                (mk_u64 0)
                                cak
                                (mk_u64 0)
                                exp
                            in
                            let hax_temp_output:Core.Result.t_Result
                              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                t13.Tls13record.t_DuplexCipherState1 &
                                t_ServerPostServerFinished) u8 =
                              Core.Result.Result_Ok
                              (sfin,
                                cipher1,
                                (ServerPostServerFinished cr sr algs ms_handle cfk tx
                                  <:
                                  t_ServerPostServerFinished)
                                <:
                                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                  t13.Tls13record.t_DuplexCipherState1 &
                                  t_ServerPostServerFinished))
                              <:
                              Core.Result.t_Result
                                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                  t13.Tls13record.t_DuplexCipherState1 &
                                  t_ServerPostServerFinished) u8
                            in
                            ks, hax_temp_output
                            <:
                            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                              Core.Result.t_Result
                                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                  t13.Tls13record.t_DuplexCipherState1 &
                                  t_ServerPostServerFinished) u8)
                          | Core.Result.Result_Err err ->
                            ks,
                            (Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result
                                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                  t13.Tls13record.t_DuplexCipherState1 &
                                  t_ServerPostServerFinished) u8)
                            <:
                            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                              Core.Result.t_Result
                                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                  t13.Tls13record.t_DuplexCipherState1 &
                                  t_ServerPostServerFinished) u8))
                      | Core.Result.Result_Err err ->
                        ks,
                        (Core.Result.Result_Err err
                          <:
                          Core.Result.t_Result
                            (t13.Tls13formats.Handshake_data.t_HandshakeData &
                              t13.Tls13record.t_DuplexCipherState1 &
                              t_ServerPostServerFinished) u8)
                        <:
                        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                          Core.Result.t_Result
                            (t13.Tls13formats.Handshake_data.t_HandshakeData &
                              t13.Tls13record.t_DuplexCipherState1 &
                              t_ServerPostServerFinished) u8))
                  | Core.Result.Result_Err err ->
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8)
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8))
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)

let put_client_finished
      (cfin: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let ServerPostServerFinished cr sr algs ms cfk tx:t_ServerPostServerFinished = st in
  match
    t13.Tls13formats.impl_Transcript__transcript_hash tx
    <:
    Core.Result.t_Result t13.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok th ->
    (match
        t13.Tls13formats.parse_finished cfin <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok vd ->
        (match
            t13.Tls13crypto.hmac_verify (t13.Tls13crypto.impl_Algorithms__hash algs
                <:
                t13.Tls13crypto.t_HashAlgorithm)
              cfk
              th
              vd
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            let tx:t13.Tls13formats.t_Transcript =
              t13.Tls13formats.impl_Transcript__add tx cfin
            in
            (match
                t13.Tls13formats.impl_Transcript__transcript_hash tx
                <:
                Core.Result.t_Result t13.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok th ->
                let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8) =
                  t13.Tls13keyscheduler.derive_rms (t13.Tls13crypto.impl_Algorithms__hash algs
                      <:
                      t13.Tls13crypto.t_HashAlgorithm)
                    ms
                    th
                    ks
                in
                let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                (match
                    out <: Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8
                  with
                  | Core.Result.Result_Ok rms ->
                    let hax_temp_output:Core.Result.t_Result t_ServerPostClientFinished u8 =
                      Core.Result.Result_Ok
                      (ServerPostClientFinished cr sr algs rms tx <: t_ServerPostClientFinished)
                      <:
                      Core.Result.t_Result t_ServerPostClientFinished u8
                    in
                    ks, hax_temp_output
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result t_ServerPostClientFinished u8)
                  | Core.Result.Result_Err err ->
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result t_ServerPostClientFinished u8)
                    <:
                    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result t_ServerPostClientFinished u8))
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err <: Core.Result.t_Result t_ServerPostClientFinished u8)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result t_ServerPostClientFinished u8))
          | Core.Result.Result_Err err ->
            ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_ServerPostClientFinished u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result t_ServerPostClientFinished u8))
      | Core.Result.Result_Err err ->
        ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_ServerPostClientFinished u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result t_ServerPostClientFinished u8))
  | Core.Result.Result_Err err ->
    ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_ServerPostClientFinished u8)
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result t_ServerPostClientFinished u8)

let server_init_no_psk
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result
      (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8) =
    put_client_hello algs ch db ks
  in
  let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  match
    out
    <:
    Core.Result.t_Result
      (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8
  with
  | Core.Result.Result_Ok (cipher0, st) ->
    let tmp0, tmp1, out:(iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8) =
      get_server_hello #iimpl_447424039_ st rng ks
    in
    let rng:iimpl_447424039_ = tmp0 in
    let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp1 in
    (match
        out
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherStateH &
            t_ServerPostServerHello) u8
      with
      | Core.Result.Result_Ok (sh, cipher_hs, st) ->
        let tmp0, out:(iimpl_447424039_ &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8) =
          get_server_signature #iimpl_447424039_ st rng
        in
        let rng:iimpl_447424039_ = tmp0 in
        (match
            out
            <:
            Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                t13.Tls13formats.Handshake_data.t_HandshakeData &
                t13.Tls13formats.Handshake_data.t_HandshakeData &
                t_ServerPostCertificateVerify) u8
          with
          | Core.Result.Result_Ok (ee, sc, scv, st) ->
            let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8) =
              get_server_finished st ks
            in
            let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
            (match
                out
                <:
                Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    t13.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8
              with
              | Core.Result.Result_Ok (sfin, cipher1, st) ->
                let flight:t13.Tls13formats.Handshake_data.t_HandshakeData =
                  t13.Tls13formats.Handshake_data.impl_HandshakeData__concat (t13.Tls13formats.Handshake_data.impl_HandshakeData__concat
                        (t13.Tls13formats.Handshake_data.impl_HandshakeData__concat ee sc
                          <:
                          t13.Tls13formats.Handshake_data.t_HandshakeData)
                        scv
                      <:
                      t13.Tls13formats.Handshake_data.t_HandshakeData)
                    sfin
                in
                let hax_temp_output:Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    t13.Tls13formats.Handshake_data.t_HandshakeData &
                    Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                    t13.Tls13record.t_DuplexCipherStateH &
                    t13.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8 =
                  Core.Result.Result_Ok
                  (sh, flight, cipher0, cipher_hs, cipher1, st
                    <:
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished))
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8
                in
                rng, ks, hax_temp_output
                <:
                (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
              | Core.Result.Result_Err err ->
                rng,
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                <:
                (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8))
          | Core.Result.Result_Err err ->
            rng,
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            <:
            (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8))
      | Core.Result.Result_Err err ->
        rng,
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
              t13.Tls13record.t_DuplexCipherStateH &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8)
        <:
        (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
              t13.Tls13record.t_DuplexCipherStateH &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))
  | Core.Result.Result_Err err ->
    rng,
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
          t13.Tls13record.t_DuplexCipherStateH &
          t13.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)
    <:
    (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
          t13.Tls13record.t_DuplexCipherStateH &
          t13.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)

let server_init_psk
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result
      (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8) =
    put_client_hello algs ch db ks
  in
  let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  match
    out
    <:
    Core.Result.t_Result
      (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8
  with
  | Core.Result.Result_Ok (cipher0, st) ->
    let tmp0, tmp1, out:(iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8) =
      get_server_hello #iimpl_447424039_ st rng ks
    in
    let rng:iimpl_447424039_ = tmp0 in
    let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp1 in
    (match
        out
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherStateH &
            t_ServerPostServerHello) u8
      with
      | Core.Result.Result_Ok (sh, cipher_hs, st) ->
        (match
            get_skip_server_signature st
            <:
            Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify)
              u8
          with
          | Core.Result.Result_Ok (ee, st) ->
            let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8) =
              get_server_finished st ks
            in
            let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
            (match
                out
                <:
                Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    t13.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8
              with
              | Core.Result.Result_Ok (sfin, cipher1, st) ->
                let flight:t13.Tls13formats.Handshake_data.t_HandshakeData =
                  t13.Tls13formats.Handshake_data.impl_HandshakeData__concat ee sfin
                in
                let hax_temp_output:Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    t13.Tls13formats.Handshake_data.t_HandshakeData &
                    Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                    t13.Tls13record.t_DuplexCipherStateH &
                    t13.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8 =
                  Core.Result.Result_Ok
                  (sh, flight, cipher0, cipher_hs, cipher1, st
                    <:
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished))
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8
                in
                rng, ks, hax_temp_output
                <:
                (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
              | Core.Result.Result_Err err ->
                rng,
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                <:
                (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8))
          | Core.Result.Result_Err err ->
            rng,
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            <:
            (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8))
      | Core.Result.Result_Err err ->
        rng,
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
              t13.Tls13record.t_DuplexCipherStateH &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8)
        <:
        (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
              t13.Tls13record.t_DuplexCipherStateH &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))
  | Core.Result.Result_Err err ->
    rng,
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
          t13.Tls13record.t_DuplexCipherStateH &
          t13.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)
    <:
    (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
          t13.Tls13record.t_DuplexCipherStateH &
          t13.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)

let server_init
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let (ks, rng), hax_temp_output:((t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      iimpl_447424039_) &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
        t13.Tls13record.t_DuplexCipherStateH &
        t13.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8) =
    match t13.Tls13crypto.impl_Algorithms__psk_mode algs <: bool with
    | false ->
      let tmp0, tmp1, out:(iimpl_447424039_ &
        t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) =
        server_init_no_psk #iimpl_447424039_ algs ch db rng ks
      in
      let rng:iimpl_447424039_ = tmp0 in
      let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp1 in
      (ks, rng <: (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler & iimpl_447424039_)), out
      <:
      ((t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler & iimpl_447424039_) &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8)
    | true ->
      let tmp0, tmp1, out:(iimpl_447424039_ &
        t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) =
        server_init_psk #iimpl_447424039_ algs ch db rng ks
      in
      let rng:iimpl_447424039_ = tmp0 in
      let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp1 in
      (ks, rng <: (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler & iimpl_447424039_)), out
      <:
      ((t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler & iimpl_447424039_) &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8)
  in
  rng, ks, hax_temp_output
  <:
  (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
        t13.Tls13record.t_DuplexCipherStateH &
        t13.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8)

let server_finish
      (cf: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result t_ServerPostClientFinished u8) =
    put_client_finished cf st ks
  in
  let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  let hax_temp_output:Core.Result.t_Result t_ServerPostClientFinished u8 = out in
  ks, hax_temp_output
  <:
  (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result t_ServerPostClientFinished u8)
