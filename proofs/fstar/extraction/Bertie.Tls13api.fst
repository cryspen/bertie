module Bertie.Tls13api
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13formats.Handshake_data in
  let open Bertie.Tls13utils in
  let open Rand_core in
  ()

let in_psk_mode (c: t_Client) =
  match c <: t_Client with
  | Client_Client0 cstate _ ->
    Bertie.Tls13crypto.impl_Algorithms__psk_mode (Bertie.Tls13handshake.algs_post_client_hello cstate

        <:
        Bertie.Tls13crypto.t_Algorithms)
  | Client_ClientH cstate _ _ _ ->
    Bertie.Tls13crypto.impl_Algorithms__psk_mode (Bertie.Tls13handshake.algs_post_server_hello cstate

        <:
        Bertie.Tls13crypto.t_Algorithms)
  | Client_Client1 cstate _ ->
    Bertie.Tls13crypto.impl_Algorithms__psk_mode (Bertie.Tls13handshake.algs_post_client_finished cstate

        <:
        Bertie.Tls13crypto.t_Algorithms)

let impl_Client__connect
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (server_name: Bertie.Tls13utils.t_Bytes)
      (session_ticket psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
     =
  let tmp0, out:(iimpl_447424039_ &
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        Bertie.Tls13handshake.t_ClientPostClientHello) u8) =
    Bertie.Tls13handshake.client_init #iimpl_447424039_
      ciphersuite
      server_name
      session_ticket
      psk
      rng
  in
  let rng:iimpl_447424039_ = tmp0 in
  match
    out
    <:
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        Bertie.Tls13handshake.t_ClientPostClientHello) u8
  with
  | Core.Result.Result_Ok (client_hello, cipherstate0, client_state) ->
    (match
        Bertie.Tls13formats.handshake_record client_hello
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok client_hello_record ->
        let client_hello_record:Bertie.Tls13utils.t_Bytes =
          Rust_primitives.Hax.update_at client_hello_record
            (mk_usize 2)
            (Bertie.Tls13utils.v_U8 (mk_u8 1) <: u8)
        in
        let hax_temp_output:Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8 =
          Core.Result.Result_Ok
          (client_hello_record, (Client_Client0 client_state cipherstate0 <: t_Client)
            <:
            (Bertie.Tls13utils.t_Bytes & t_Client))
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8
        in
        rng, hax_temp_output
        <:
        (iimpl_447424039_ & Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8)
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8)
        <:
        (iimpl_447424039_ & Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err <: Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8)
    <:
    (iimpl_447424039_ & Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8)

let impl_Client__read_handshake (self: t_Client) (handshake_bytes: Bertie.Tls13utils.t_Bytes) =
  match self <: t_Client with
  | Client_Client0 state cipher_state ->
    (match
        Bertie.Tls13formats.get_handshake_record handshake_bytes
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
      with
      | Core.Result.Result_Ok sf ->
        (match
            Bertie.Tls13handshake.client_set_params sf state
            <:
            Core.Result.t_Result
              (Bertie.Tls13record.t_DuplexCipherStateH &
                Bertie.Tls13handshake.t_ClientPostServerHello) u8
          with
          | Core.Result.Result_Ok (cipher1, cstate) ->
            let buf:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
              Core.Convert.f_from #Bertie.Tls13formats.Handshake_data.t_HandshakeData
                #Bertie.Tls13utils.t_Bytes
                #FStar.Tactics.Typeclasses.solve
                (Bertie.Tls13utils.impl_Bytes__new () <: Bertie.Tls13utils.t_Bytes)
            in
            Core.Result.Result_Ok
            ((Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
              (Client_ClientH cstate cipher_state cipher1 buf <: t_Client)
              <:
              (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client))
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client) u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client) u8)
  | Client_ClientH cstate cipher0 cipher_hs buf ->
    (match
        Bertie.Tls13record.decrypt_handshake handshake_bytes cipher_hs
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherStateH) u8
      with
      | Core.Result.Result_Ok (hd, cipher_hs) ->
        let buf:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
          Bertie.Tls13formats.Handshake_data.impl_HandshakeData__concat buf hd
        in
        if
          Bertie.Tls13formats.Handshake_data.impl_HandshakeData__find_handshake_message buf
            (Bertie.Tls13formats.Handshake_data.HandshakeType_Finished
              <:
              Bertie.Tls13formats.Handshake_data.t_HandshakeType)
            (mk_usize 0)
        then
          match
            Bertie.Tls13handshake.client_finish buf cstate
            <:
            Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Bertie.Tls13record.t_DuplexCipherState1 &
                Bertie.Tls13handshake.t_ClientPostClientFinished) u8
          with
          | Core.Result.Result_Ok (cfin, cipher1, cstate) ->
            (match
                Bertie.Tls13record.encrypt_handshake cfin (mk_usize 0) cipher_hs
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13record.t_DuplexCipherStateH) u8
              with
              | Core.Result.Result_Ok (cf_rec, e_cipher_hs) ->
                Core.Result.Result_Ok
                ((Core.Option.Option_Some cf_rec <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
                  (Client_Client1 cstate cipher1 <: t_Client)
                  <:
                  (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client))
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client) u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client) u8
        else
          Core.Result.Result_Ok
          ((Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
            (Client_ClientH cstate cipher0 cipher_hs buf <: t_Client)
            <:
            (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client))
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client) u8)
  | _ ->
    Core.Result.Result_Err Bertie.Tls13utils.v_INCORRECT_STATE
    <:
    Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & t_Client) u8

let impl_Client__read (self: t_Client) (message_bytes: Bertie.Tls13utils.t_Bytes) =
  match self <: t_Client with
  | Client_Client1 state cipher1 ->
    (match
        Bertie.Tls13record.decrypt_data_or_hs message_bytes cipher1
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13record.t_DuplexCipherState1) u8
      with
      | Core.Result.Result_Ok (ty, hd, cipher1) ->
        (match ty <: Bertie.Tls13formats.t_ContentType with
          | Bertie.Tls13formats.ContentType_ApplicationData  ->
            Core.Result.Result_Ok
            ((Core.Option.Option_Some (Bertie.Tls13utils.impl_AppData__new hd)
                <:
                Core.Option.t_Option Bertie.Tls13utils.t_AppData),
              (Client_Client1 state cipher1 <: t_Client)
              <:
              (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Client))
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Client) u8
          | Bertie.Tls13formats.ContentType_Handshake  ->
            Core.Result.Result_Ok
            ((Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_AppData),
              (Client_Client1 state cipher1 <: t_Client)
              <:
              (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Client))
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Client) u8
          | _ ->
            Core.Result.Result_Err Bertie.Tls13utils.v_PARSE_FAILED
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Client) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Client) u8)
  | _ ->
    Core.Result.Result_Err Bertie.Tls13utils.v_INCORRECT_STATE
    <:
    Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Client) u8

let impl_Client__write (self: t_Client) (application_data: Bertie.Tls13utils.t_AppData) =
  match self <: t_Client with
  | Client_Client1 cstate cipher1 ->
    (match
        Bertie.Tls13record.encrypt_data application_data (mk_usize 0) cipher1
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13record.t_DuplexCipherState1)
          u8
      with
      | Core.Result.Result_Ok (v_by, cipher1) ->
        Core.Result.Result_Ok
        (v_by, (Client_Client1 cstate cipher1 <: t_Client) <: (Bertie.Tls13utils.t_Bytes & t_Client)
        )
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8
    )
  | _ ->
    Core.Result.Result_Err Bertie.Tls13utils.v_INCORRECT_STATE
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Client) u8

let impl_Server__read_handshake (self: t_Server) (handshake_bytes: Bertie.Tls13utils.t_Bytes) =
  match self <: t_Server with
  | Server_ServerH sstate e_cipher0 cipher_hs cipher1 ->
    (match
        Bertie.Tls13record.decrypt_handshake handshake_bytes cipher_hs
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherStateH) u8
      with
      | Core.Result.Result_Ok (cf, e_cipher_hs) ->
        (match
            Bertie.Tls13handshake.server_finish cf sstate
            <:
            Core.Result.t_Result Bertie.Tls13handshake.t_ServerPostClientFinished u8
          with
          | Core.Result.Result_Ok sstate ->
            Core.Result.Result_Ok (Server_Server1 sstate cipher1 <: t_Server)
            <:
            Core.Result.t_Result t_Server u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result t_Server u8)
      | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result t_Server u8
    )
  | _ ->
    Core.Result.Result_Err Bertie.Tls13utils.v_INCORRECT_STATE <: Core.Result.t_Result t_Server u8

let impl_Server__write (self: t_Server) (application_data: Bertie.Tls13utils.t_AppData) =
  match self <: t_Server with
  | Server_Server1 sstate cipher1 ->
    (match
        Bertie.Tls13record.encrypt_data application_data (mk_usize 0) cipher1
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13record.t_DuplexCipherState1)
          u8
      with
      | Core.Result.Result_Ok (v_by, cipher1) ->
        Core.Result.Result_Ok
        (v_by, (Server_Server1 sstate cipher1 <: t_Server) <: (Bertie.Tls13utils.t_Bytes & t_Server)
        )
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Server) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Server) u8
    )
  | _ ->
    Core.Result.Result_Err Bertie.Tls13utils.v_INCORRECT_STATE
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_Server) u8

let impl_Server__read (self: t_Server) (application_data: Bertie.Tls13utils.t_Bytes) =
  match self <: t_Server with
  | Server_Server1 sstate cipher1 ->
    (match
        Bertie.Tls13record.decrypt_data application_data cipher1
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_AppData & Bertie.Tls13record.t_DuplexCipherState1)
          u8
      with
      | Core.Result.Result_Ok (ad, cipher1) ->
        Core.Result.Result_Ok
        ((Core.Option.Option_Some ad <: Core.Option.t_Option Bertie.Tls13utils.t_AppData),
          (Server_Server1 sstate cipher1 <: t_Server)
          <:
          (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Server))
        <:
        Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Server) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Server) u8)
  | _ ->
    Core.Result.Result_Err Bertie.Tls13utils.v_INCORRECT_STATE
    <:
    Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_AppData & t_Server) u8

let impl_Server__accept
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (db: Bertie.Server.t_ServerDB)
      (client_hello: Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
     =
  let ch_rec:Bertie.Tls13utils.t_Bytes =
    Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve client_hello
  in
  let ch_rec:Bertie.Tls13utils.t_Bytes =
    Rust_primitives.Hax.update_at ch_rec (mk_usize 2) (Bertie.Tls13utils.v_U8 (mk_u8 3) <: u8)
  in
  match
    Bertie.Tls13formats.get_handshake_record ch_rec
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok ch ->
    let tmp0, out:(iimpl_447424039_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
          Bertie.Tls13record.t_DuplexCipherStateH &
          Bertie.Tls13record.t_DuplexCipherState1 &
          Bertie.Tls13handshake.t_ServerPostServerFinished) u8) =
      Bertie.Tls13handshake.server_init #iimpl_447424039_ ciphersuite ch db rng
    in
    let rng:iimpl_447424039_ = tmp0 in
    (match
        out
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
            Bertie.Tls13record.t_DuplexCipherStateH &
            Bertie.Tls13record.t_DuplexCipherState1 &
            Bertie.Tls13handshake.t_ServerPostServerFinished) u8
      with
      | Core.Result.Result_Ok (server_hello, server_finished, cipher0, cipher_hs, cipher1, sstate) ->
        (match
            Bertie.Tls13formats.handshake_record server_hello
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok sh_rec ->
            (match
                Bertie.Tls13record.encrypt_handshake server_finished (mk_usize 0) cipher_hs
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13record.t_DuplexCipherStateH) u8
              with
              | Core.Result.Result_Ok (sf_rec, cipher_hs) ->
                let hax_temp_output:Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8 =
                  Core.Result.Result_Ok
                  (sh_rec, sf_rec, (Server_ServerH sstate cipher0 cipher_hs cipher1 <: t_Server)
                    <:
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server))
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8
                in
                rng, hax_temp_output
                <:
                (iimpl_447424039_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8)
              | Core.Result.Result_Err err ->
                rng,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8)
                <:
                (iimpl_447424039_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8))
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8)
            <:
            (iimpl_447424039_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8
        )
        <:
        (iimpl_447424039_ &
          Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8
        ))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8)
    <:
    (iimpl_447424039_ &
      Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & t_Server) u8)
