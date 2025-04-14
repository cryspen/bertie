module t13.Tls13api
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open t13.Tls13formats.Handshake_data in
  let open t13.Tls13utils in
  let open Rand_core in
  ()

let in_psk_mode (c: t_Client) =
  match c <: t_Client with
  | Client_Client0 cstate _ ->
    t13.Tls13crypto.impl_Algorithms__psk_mode (t13.Tls13handshake.algs_post_client_hello cstate

        <:
        t13.Tls13crypto.t_Algorithms)
  | Client_ClientH cstate _ _ _ ->
    t13.Tls13crypto.impl_Algorithms__psk_mode (t13.Tls13handshake.algs_post_server_hello cstate

        <:
        t13.Tls13crypto.t_Algorithms)
  | Client_Client1 cstate _ ->
    t13.Tls13crypto.impl_Algorithms__psk_mode (t13.Tls13handshake.algs_post_client_finished cstate

        <:
        t13.Tls13crypto.t_Algorithms)

let impl_Client__connect
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (server_name: t13.Tls13utils.t_Bytes)
      (session_ticket psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, tmp1, out:(iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
        t13.Tls13handshake.t_ClientPostClientHello) u8) =
    t13.Tls13handshake.client_init #iimpl_447424039_
      ciphersuite
      server_name
      session_ticket
      psk
      rng
      ks
  in
  let rng:iimpl_447424039_ = tmp0 in
  let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp1 in
  match
    out
    <:
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
        t13.Tls13handshake.t_ClientPostClientHello) u8
  with
  | Core.Result.Result_Ok (client_hello, cipherstate0, client_state) ->
    (match
        t13.Tls13formats.handshake_record client_hello
        <:
        Core.Result.t_Result t13.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok client_hello_record ->
        let client_hello_record:t13.Tls13utils.t_Bytes =
          Rust_primitives.Hax.update_at client_hello_record
            (mk_usize 2)
            (t13.Tls13utils.v_U8 (mk_u8 1) <: u8)
        in
        let hax_temp_output:Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8 =
          Core.Result.Result_Ok
          (client_hello_record, (Client_Client0 client_state cipherstate0 <: t_Client)
            <:
            (t13.Tls13utils.t_Bytes & t_Client))
          <:
          Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8
        in
        rng, ks, hax_temp_output
        <:
        (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8)
      | Core.Result.Result_Err err ->
        rng,
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8)
        <:
        (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8))
  | Core.Result.Result_Err err ->
    rng,
    ks,
    (Core.Result.Result_Err err <: Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8)
    <:
    (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8)

let impl_Client__read_handshake
      (self: t_Client)
      (handshake_bytes: t13.Tls13utils.t_Bytes)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  match self <: t_Client with
  | Client_Client0 state cipher_state ->
    (match
        t13.Tls13formats.get_handshake_record handshake_bytes
        <:
        Core.Result.t_Result t13.Tls13formats.Handshake_data.t_HandshakeData u8
      with
      | Core.Result.Result_Ok sf ->
        let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (t13.Tls13record.t_DuplexCipherStateH & t13.Tls13handshake.t_ClientPostServerHello
            ) u8) =
          t13.Tls13handshake.client_set_params sf state ks
        in
        let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
        (match
            out
            <:
            Core.Result.t_Result
              (t13.Tls13record.t_DuplexCipherStateH &
                t13.Tls13handshake.t_ClientPostServerHello) u8
          with
          | Core.Result.Result_Ok (cipher1, cstate) ->
            let buf:t13.Tls13formats.Handshake_data.t_HandshakeData =
              Core.Convert.f_from #t13.Tls13formats.Handshake_data.t_HandshakeData
                #t13.Tls13utils.t_Bytes
                #FStar.Tactics.Typeclasses.solve
                (t13.Tls13utils.impl_Bytes__new () <: t13.Tls13utils.t_Bytes)
            in
            ks,
            (Core.Result.Result_Ok
              ((Core.Option.Option_None <: Core.Option.t_Option t13.Tls13utils.t_Bytes),
                (Client_ClientH cstate cipher_state cipher1 buf <: t_Client)
                <:
                (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client))
              <:
              Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8))
  | Client_ClientH cstate cipher0 cipher_hs buf ->
    (match
        t13.Tls13record.decrypt_handshake handshake_bytes cipher_hs
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherStateH) u8
      with
      | Core.Result.Result_Ok (hd, cipher_hs) ->
        let buf:t13.Tls13formats.Handshake_data.t_HandshakeData =
          t13.Tls13formats.Handshake_data.impl_HandshakeData__concat buf hd
        in
        if
          t13.Tls13formats.Handshake_data.impl_HandshakeData__find_handshake_message buf
            (t13.Tls13formats.Handshake_data.HandshakeType_Finished
              <:
              t13.Tls13formats.Handshake_data.t_HandshakeType)
            (mk_usize 0)
        then
          let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
            Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                t13.Tls13record.t_DuplexCipherState1 &
                t13.Tls13handshake.t_ClientPostClientFinished) u8) =
            t13.Tls13handshake.client_finish buf cstate ks
          in
          let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
          match
            out
            <:
            Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                t13.Tls13record.t_DuplexCipherState1 &
                t13.Tls13handshake.t_ClientPostClientFinished) u8
          with
          | Core.Result.Result_Ok (cfin, cipher1, cstate) ->
            (match
                t13.Tls13record.encrypt_handshake cfin (mk_usize 0) cipher_hs
                <:
                Core.Result.t_Result
                  (t13.Tls13utils.t_Bytes & t13.Tls13record.t_DuplexCipherStateH) u8
              with
              | Core.Result.Result_Ok (cf_rec, e_cipher_hs) ->
                ks,
                (Core.Result.Result_Ok
                  ((Core.Option.Option_Some cf_rec <: Core.Option.t_Option t13.Tls13utils.t_Bytes
                    ),
                    (Client_Client1 cstate cipher1 <: t_Client)
                    <:
                    (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client))
                  <:
                  Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client)
                    u8)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client)
                    u8)
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client)
                    u8)
                <:
                (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client)
                    u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
        else
          ks,
          (Core.Result.Result_Ok
            ((Core.Option.Option_None <: Core.Option.t_Option t13.Tls13utils.t_Bytes),
              (Client_ClientH cstate cipher0 cipher_hs buf <: t_Client)
              <:
              (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client))
            <:
            Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
          <:
          (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
            Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8))
  | _ ->
    ks,
    (Core.Result.Result_Err t13.Tls13utils.v_INCORRECT_STATE
      <:
      Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)

let impl_Client__read (self: t_Client) (message_bytes: t13.Tls13utils.t_Bytes) =
  match self <: t_Client with
  | Client_Client1 state cipher1 ->
    (match
        t13.Tls13record.decrypt_data_or_hs message_bytes cipher1
        <:
        Core.Result.t_Result
          (t13.Tls13formats.t_ContentType & t13.Tls13utils.t_Bytes &
            t13.Tls13record.t_DuplexCipherState1) u8
      with
      | Core.Result.Result_Ok (ty, hd, cipher1) ->
        (match ty <: t13.Tls13formats.t_ContentType with
          | t13.Tls13formats.ContentType_ApplicationData  ->
            Core.Result.Result_Ok
            ((Core.Option.Option_Some (t13.Tls13utils.impl_AppData__new hd)
                <:
                Core.Option.t_Option t13.Tls13utils.t_AppData),
              (Client_Client1 state cipher1 <: t_Client)
              <:
              (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Client))
            <:
            Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Client) u8
          | t13.Tls13formats.ContentType_Handshake  ->
            Core.Result.Result_Ok
            ((Core.Option.Option_None <: Core.Option.t_Option t13.Tls13utils.t_AppData),
              (Client_Client1 state cipher1 <: t_Client)
              <:
              (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Client))
            <:
            Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Client) u8
          | _ ->
            Core.Result.Result_Err t13.Tls13utils.v_PARSE_FAILED
            <:
            Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Client) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Client) u8)
  | _ ->
    Core.Result.Result_Err t13.Tls13utils.v_INCORRECT_STATE
    <:
    Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Client) u8

let impl_Client__write (self: t_Client) (application_data: t13.Tls13utils.t_AppData) =
  match self <: t_Client with
  | Client_Client1 cstate cipher1 ->
    (match
        t13.Tls13record.encrypt_data application_data (mk_usize 0) cipher1
        <:
        Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13record.t_DuplexCipherState1)
          u8
      with
      | Core.Result.Result_Ok (v_by, cipher1) ->
        Core.Result.Result_Ok
        (v_by, (Client_Client1 cstate cipher1 <: t_Client) <: (t13.Tls13utils.t_Bytes & t_Client)
        )
        <:
        Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8
    )
  | _ ->
    Core.Result.Result_Err t13.Tls13utils.v_INCORRECT_STATE
    <:
    Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8

let impl_Server__read_handshake
      (self: t_Server)
      (handshake_bytes: t13.Tls13utils.t_Bytes)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  match self <: t_Server with
  | Server_ServerH sstate e_cipher0 cipher_hs cipher1 ->
    (match
        t13.Tls13record.decrypt_handshake handshake_bytes cipher_hs
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherStateH) u8
      with
      | Core.Result.Result_Ok (cf, e_cipher_hs) ->
        let tmp0, out:(t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result t13.Tls13handshake.t_ServerPostClientFinished u8) =
          t13.Tls13handshake.server_finish cf sstate ks
        in
        let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
        (match out <: Core.Result.t_Result t13.Tls13handshake.t_ServerPostClientFinished u8 with
          | Core.Result.Result_Ok sstate ->
            ks,
            (Core.Result.Result_Ok (Server_Server1 sstate cipher1 <: t_Server)
              <:
              Core.Result.t_Result t_Server u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result t_Server u8)
          | Core.Result.Result_Err err ->
            ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_Server u8)
            <:
            (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result t_Server u8))
      | Core.Result.Result_Err err ->
        ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_Server u8)
        <:
        (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler & Core.Result.t_Result t_Server u8)
    )
  | _ ->
    ks,
    (Core.Result.Result_Err t13.Tls13utils.v_INCORRECT_STATE <: Core.Result.t_Result t_Server u8)
    <:
    (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler & Core.Result.t_Result t_Server u8)

let impl_Server__write (self: t_Server) (application_data: t13.Tls13utils.t_AppData) =
  match self <: t_Server with
  | Server_Server1 sstate cipher1 ->
    (match
        t13.Tls13record.encrypt_data application_data (mk_usize 0) cipher1
        <:
        Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13record.t_DuplexCipherState1)
          u8
      with
      | Core.Result.Result_Ok (v_by, cipher1) ->
        Core.Result.Result_Ok
        (v_by, (Server_Server1 sstate cipher1 <: t_Server) <: (t13.Tls13utils.t_Bytes & t_Server)
        )
        <:
        Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Server) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Server) u8
    )
  | _ ->
    Core.Result.Result_Err t13.Tls13utils.v_INCORRECT_STATE
    <:
    Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Server) u8

let impl_Server__read (self: t_Server) (application_data: t13.Tls13utils.t_Bytes) =
  match self <: t_Server with
  | Server_Server1 sstate cipher1 ->
    (match
        t13.Tls13record.decrypt_data application_data cipher1
        <:
        Core.Result.t_Result (t13.Tls13utils.t_AppData & t13.Tls13record.t_DuplexCipherState1)
          u8
      with
      | Core.Result.Result_Ok (ad, cipher1) ->
        Core.Result.Result_Ok
        ((Core.Option.Option_Some ad <: Core.Option.t_Option t13.Tls13utils.t_AppData),
          (Server_Server1 sstate cipher1 <: t_Server)
          <:
          (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Server))
        <:
        Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Server) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Server) u8)
  | _ ->
    Core.Result.Result_Err t13.Tls13utils.v_INCORRECT_STATE
    <:
    Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Server) u8

let impl_Server__accept
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (db: t13.Server.t_ServerDB)
      (client_hello: t13.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let ch_rec:t13.Tls13utils.t_Bytes =
    Core.Clone.f_clone #t13.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve client_hello
  in
  let ch_rec:t13.Tls13utils.t_Bytes =
    Rust_primitives.Hax.update_at ch_rec (mk_usize 2) (t13.Tls13utils.v_U8 (mk_u8 3) <: u8)
  in
  match
    t13.Tls13formats.get_handshake_record ch_rec
    <:
    Core.Result.t_Result t13.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok ch ->
    let tmp0, tmp1, out:(iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
          t13.Tls13record.t_DuplexCipherStateH &
          t13.Tls13record.t_DuplexCipherState1 &
          t13.Tls13handshake.t_ServerPostServerFinished) u8) =
      t13.Tls13handshake.server_init #iimpl_447424039_ ciphersuite ch db rng ks
    in
    let rng:iimpl_447424039_ = tmp0 in
    let ks:t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp1 in
    (match
        out
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t13.Tls13handshake.t_ServerPostServerFinished) u8
      with
      | Core.Result.Result_Ok (server_hello, server_finished, cipher0, cipher_hs, cipher1, sstate) ->
        (match
            t13.Tls13formats.handshake_record server_hello
            <:
            Core.Result.t_Result t13.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok sh_rec ->
            (match
                t13.Tls13record.encrypt_handshake server_finished (mk_usize 0) cipher_hs
                <:
                Core.Result.t_Result
                  (t13.Tls13utils.t_Bytes & t13.Tls13record.t_DuplexCipherStateH) u8
              with
              | Core.Result.Result_Ok (sf_rec, cipher_hs) ->
                let hax_temp_output:Core.Result.t_Result
                  (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8 =
                  Core.Result.Result_Ok
                  (sh_rec, sf_rec, (Server_ServerH sstate cipher0 cipher_hs cipher1 <: t_Server)
                    <:
                    (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server))
                  <:
                  Core.Result.t_Result
                    (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8
                in
                rng, ks, hax_temp_output
                <:
                (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8)
              | Core.Result.Result_Err err ->
                rng,
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8)
                <:
                (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8))
          | Core.Result.Result_Err err ->
            rng,
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8)
            <:
            (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8))
      | Core.Result.Result_Err err ->
        rng,
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8
        )
        <:
        (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8
        ))
  | Core.Result.Result_Err err ->
    rng,
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8)
    <:
    (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8)
