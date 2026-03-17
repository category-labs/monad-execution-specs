open Monad_lib
open Numeric
open Byte_string

module Stubs (I : Cstubs_inverted.INTERNAL) = struct
  open Ctypes
  module type BYTES = sig
    type t
    val byte_width : int
    val init : (int -> char) -> t
    val to_bytes : t -> Bytes.t
  end
  module Byte_View (B : BYTES) = struct
    type t = B.t

    type repr
    let repr : repr structure typ = structure (Format.sprintf "bytes%d_t" B.byte_width)
    let bytes = field repr "bytes" (array B.byte_width uint8_t)
    let () = seal repr
    let () = I.structure repr

    let c_of_ocaml (value : B.t) : repr structure =
      let value_bytes = B.to_bytes value in
      let c = make repr in
      for i = 0 to B.byte_width - 1 do
        CArray.set (getf c bytes) i (Unsigned.UInt8.of_int (Char.code value_bytes.[i]))
      done ;
      c

    let ocaml_of_c (value : repr structure) : B.t =
      let arr = getf value bytes in
      B.init (fun i -> Char.chr (Unsigned.UInt8.to_int (CArray.get arr i)))

    let t = view ~read:ocaml_of_c ~write:c_of_ocaml repr
  end

  module C_B32 = Byte_View (B32)
  module C_Address = Byte_View (Chain.Ethereum.Address)

  module C_Client = struct
    type t = Fuzz_client.t
    type repr
    let repr : repr structure typ = structure "RunLoopFuzzClient"
    let () = I.structure repr

    let c_of_ocaml (value : t) : repr structure ptr = from_voidp repr (Root.create value)
    let ocaml_of_c (value : repr structure ptr) : t = Root.get (to_voidp value)
    let t = view ~read:ocaml_of_c ~write:c_of_ocaml (ptr repr)
  end

  let runloop_fuzz_client_new (chain_id : Unsigned.UInt64.t) (ledger_path : string) : Fuzz_client.t =
    let chain_id = Uint.of_uint64 (Unsigned.UInt64.to_int64 chain_id) in
    Fuzz_client.make ~chain_id ~ledger_path
  let () =
    I.internal "runloop_fuzz_client_new"
      (uint64_t @-> string @-> returning C_Client.t)
      runloop_fuzz_client_new

  let runloop_fuzz_client_delete (client : C_Client.repr structure ptr) = Root.release (to_voidp client)
  let () =
    I.internal "runloop_fuzz_client_delete" (ptr C_Client.repr @-> returning void) runloop_fuzz_client_delete

  let runloop_fuzz_client_run (client : C_Client.t) (n_blocks : Unsigned.UInt64.t) =
    Fuzz_client.run client (Unsigned.UInt64.to_int n_blocks)
  let () =
    I.internal "runloop_fuzz_client_run" (C_Client.t @-> uint64_t @-> returning void) runloop_fuzz_client_run

  let runloop_fuzz_client_set_balance (client : C_Client.t) (addr : C_Address.t ptr) (balance : C_B32.t ptr) :
      unit =
    Fuzz_client.set_balance client !@addr (U256.of_repr !@balance)
  let () =
    I.internal "runloop_fuzz_client_set_balance"
      (C_Client.t @-> ptr (const C_Address.t) @-> ptr (const C_B32.t) @-> returning void)
      runloop_fuzz_client_set_balance

  let runloop_fuzz_client_get_balance
      (client : C_Client.t) (addr : C_Address.t ptr) (balance_out : C_B32.t ptr) =
    balance_out <-@ U256.to_repr (Fuzz_client.get_balance client !@addr)
  let () =
    I.internal "runloop_fuzz_client_get_balance"
      (C_Client.t @-> ptr (const C_Address.t) @-> ptr C_B32.t @-> returning void)
      runloop_fuzz_client_get_balance

  let runloop_fuzz_client_get_state_root (client : C_Client.t) (state_root_out : C_B32.t ptr) =
    state_root_out <-@ Fuzz_client.get_state_root client
  let () =
    I.internal "runloop_fuzz_client_get_state_root"
      (C_Client.t @-> ptr C_B32.t @-> returning void)
      runloop_fuzz_client_get_state_root

  let runloop_fuzz_client_generate_test_fixture (client : C_Client.t) (filename : string) =
    Fuzz_client.generate_test_fixture client filename
  let () =
    I.internal "runloop_fuzz_client_generate_test_fixture"
      (C_Client.t @-> string @-> returning void)
      runloop_fuzz_client_generate_test_fixture

  let runloop_fuzz_client_dump (client : C_Client.t) =
    client.chain.accounts
    |> B20.Map.to_yojson Chain.Ethereum.Account.to_yojson
    |> Yojson.Safe.pretty_to_string
    |> Format.printf "%s\n" ;
    Format.print_flush ()
  let () = I.internal "runloop_fuzz_client_dump" (C_Client.t @-> returning void) runloop_fuzz_client_dump
end
