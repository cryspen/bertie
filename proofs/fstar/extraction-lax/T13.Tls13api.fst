module t13.Tls13api
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let in_psk_mode (c: t_Client) =
  match c with
  | Client_Client0 cstate _ ->
    t13.Tls13crypto.impl__Algorithms__psk_mode (t13.Tls13handshake.algs_post_client_hello cstate

        <:
        t13.Tls13crypto.t_Algorithms)
  | Client_ClientH cstate _ _ _ ->
    t13.Tls13crypto.impl__Algorithms__psk_mode (t13.Tls13handshake.algs_post_server_hello cstate

        <:
        t13.Tls13crypto.t_Algorithms)
  | Client_Client1 cstate _ ->
    t13.Tls13crypto.impl__Algorithms__psk_mode (t13.Tls13handshake.algs_post_client_finished cstate

        <:
        t13.Tls13crypto.t_Algorithms)

let impl__Client__connect
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (server_name: t13.Tls13utils.t_Bytes)
      (session_ticket psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
     =
  let tmp0, out:(impl_916461611_ &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
        t13.Tls13handshake.t_ClientPostClientHello) u8) =
    t13.Tls13handshake.client_init ciphersuite server_name session_ticket psk rng
  in
  let rng:impl_916461611_ = tmp0 in
  match out with
  | Core.Result.Result_Ok (client_hello, cipherstate0, client_state) ->
    (match t13.Tls13formats.handshake_record client_hello with
      | Core.Result.Result_Ok client_hello_record ->
        let client_hello_record:t13.Tls13utils.t_Bytes =
          Rust_primitives.Hax.update_at client_hello_record
            (sz 2)
            (t13.Tls13utils.v_U8 1uy <: u8)
        in
        let hax_temp_output:Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8 =
          Core.Result.Result_Ok
          (client_hello_record, (Client_Client0 client_state cipherstate0 <: t_Client)
            <:
            (t13.Tls13utils.t_Bytes & t_Client))
          <:
          Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8
        in
        rng, hax_temp_output
        <:
        (impl_916461611_ & Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8)
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8)
        <:
        (impl_916461611_ & Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err <: Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8)
    <:
    (impl_916461611_ & Core.Result.t_Result (t13.Tls13utils.t_Bytes & t_Client) u8)

let impl__Server__read (self: t_Server) (application_data: t13.Tls13utils.t_Bytes) =
  match self with
  | Server_Server1 sstate cipher1 ->
    (match t13.Tls13record.decrypt_data application_data cipher1 with
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

let impl__Client__read (self: t_Client) (message_bytes: t13.Tls13utils.t_Bytes) =
  match self with
  | Client_Client1 state cipher1 ->
    (match t13.Tls13record.decrypt_data_or_hs message_bytes cipher1 with
      | Core.Result.Result_Ok (ty, hd, cipher1) ->
        (match ty with
          | t13.Tls13formats.ContentType_ApplicationData  ->
            Core.Result.Result_Ok
            ((Core.Option.Option_Some (t13.Tls13utils.impl__AppData__new hd)
                <:
                Core.Option.t_Option t13.Tls13utils.t_AppData),
              (Client_Client1 state cipher1 <: t_Client)
              <:
              (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Client))
            <:
            Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_AppData & t_Client) u8
          | t13.Tls13formats.ContentType_Handshake  ->
            let _:Prims.unit =
              Std.Io.Stdio.v__eprint (Core.Fmt.impl_2__new_const (Rust_primitives.unsize (let list =
                            ["Received Session Ticket\n"]
                          in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                      <:
                      t_Slice string)
                  <:
                  Core.Fmt.t_Arguments)
            in
            let _:Prims.unit = () in
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

let impl__Server__read_handshake (self: t_Server) (handshake_bytes: t13.Tls13utils.t_Bytes) =
  match self with
  | Server_ServerH sstate v__cipher0 cipher_hs cipher1 ->
    (match t13.Tls13record.decrypt_handshake handshake_bytes cipher_hs with
      | Core.Result.Result_Ok (cf, v__cipher_hs) ->
        (match t13.Tls13handshake.server_finish cf sstate with
          | Core.Result.Result_Ok sstate ->
            Core.Result.Result_Ok (Server_Server1 sstate cipher1 <: t_Server)
            <:
            Core.Result.t_Result t_Server u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result t_Server u8)
      | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result t_Server u8
    )
  | _ ->
    Core.Result.Result_Err t13.Tls13utils.v_INCORRECT_STATE <: Core.Result.t_Result t_Server u8

let impl__Client__write (self: t_Client) (application_data: t13.Tls13utils.t_AppData) =
  match self with
  | Client_Client1 cstate cipher1 ->
    (match t13.Tls13record.encrypt_data application_data (sz 0) cipher1 with
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

let impl__Server__write (self: t_Server) (application_data: t13.Tls13utils.t_AppData) =
  match self with
  | Server_Server1 sstate cipher1 ->
    (match t13.Tls13record.encrypt_data application_data (sz 0) cipher1 with
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

let impl__Client__read_handshake (self: t_Client) (handshake_bytes: t13.Tls13utils.t_Bytes) =
  match self with
  | Client_Client0 state cipher_state ->
    (match t13.Tls13formats.get_handshake_record handshake_bytes with
      | Core.Result.Result_Ok sf ->
        (match t13.Tls13handshake.client_set_params sf state with
          | Core.Result.Result_Ok (cipher1, cstate) ->
            let buf:t13.Tls13formats.Handshake_data.t_HandshakeData =
              Core.Convert.f_from (t13.Tls13utils.impl__Bytes__new ()
                  <:
                  t13.Tls13utils.t_Bytes)
            in
            Core.Result.Result_Ok
            ((Core.Option.Option_None <: Core.Option.t_Option t13.Tls13utils.t_Bytes),
              (Client_ClientH cstate cipher_state cipher1 buf <: t_Client)
              <:
              (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client))
            <:
            Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
  | Client_ClientH cstate cipher0 cipher_hs buf ->
    (match t13.Tls13record.decrypt_handshake handshake_bytes cipher_hs with
      | Core.Result.Result_Ok (hd, cipher_hs) ->
        let buf:t13.Tls13formats.Handshake_data.t_HandshakeData =
          t13.Tls13formats.Handshake_data.impl__HandshakeData__concat buf hd
        in
        if
          t13.Tls13formats.Handshake_data.impl__HandshakeData__find_handshake_message buf
            (t13.Tls13formats.Handshake_data.HandshakeType_Finished
              <:
              t13.Tls13formats.Handshake_data.t_HandshakeType)
            (sz 0)
        then
          match t13.Tls13handshake.client_finish buf cstate with
          | Core.Result.Result_Ok (cfin, cipher1, cstate) ->
            (match t13.Tls13record.encrypt_handshake cfin (sz 0) cipher_hs with
              | Core.Result.Result_Ok (cf_rec, v__cipher_hs) ->
                Core.Result.Result_Ok
                ((Core.Option.Option_Some cf_rec <: Core.Option.t_Option t13.Tls13utils.t_Bytes),
                  (Client_Client1 cstate cipher1 <: t_Client)
                  <:
                  (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client))
                <:
                Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8
        else
          Core.Result.Result_Ok
          ((Core.Option.Option_None <: Core.Option.t_Option t13.Tls13utils.t_Bytes),
            (Client_ClientH cstate cipher0 cipher_hs buf <: t_Client)
            <:
            (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client))
          <:
          Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8)
  | _ ->
    Core.Result.Result_Err t13.Tls13utils.v_INCORRECT_STATE
    <:
    Core.Result.t_Result (Core.Option.t_Option t13.Tls13utils.t_Bytes & t_Client) u8

let impl__Server__accept
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (db: t13.Server.t_ServerDB)
      (client_hello: t13.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
     =
  let ch_rec:t13.Tls13utils.t_Bytes = Core.Clone.f_clone client_hello in
  let ch_rec:t13.Tls13utils.t_Bytes =
    Rust_primitives.Hax.update_at ch_rec (sz 2) (t13.Tls13utils.v_U8 3uy <: u8)
  in
  match t13.Tls13formats.get_handshake_record ch_rec with
  | Core.Result.Result_Ok ch ->
    let tmp0, out:(impl_916461611_ &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
          t13.Tls13record.t_DuplexCipherStateH &
          t13.Tls13record.t_DuplexCipherState1 &
          t13.Tls13handshake.t_ServerPostServerFinished) u8) =
      t13.Tls13handshake.server_init ciphersuite ch db rng
    in
    let rng:impl_916461611_ = tmp0 in
    (match out with
      | Core.Result.Result_Ok (server_hello, server_finished, cipher0, cipher_hs, cipher1, sstate) ->
        (match t13.Tls13formats.handshake_record server_hello with
          | Core.Result.Result_Ok sh_rec ->
            (match t13.Tls13record.encrypt_handshake server_finished (sz 0) cipher_hs with
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
                rng, hax_temp_output
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8)
              | Core.Result.Result_Err err ->
                rng,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8))
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8
        )
        <:
        (impl_916461611_ &
          Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8
        ))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8)
    <:
    (impl_916461611_ &
      Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes & t_Server) u8)
