open Ctypes
open Foreign

open Byte_string

let librvcode_so = Dl.dlopen ~filename:"librvcode.so" ~flags:[RTLD_NOW; RTLD_GLOBAL]

let foreign = foreign ~from:librvcode_so

module Opaque () : sig
  type t
  val t : t typ
end = struct
  type t = unit ptr
  let t = ptr void
end

let ( .@() ) obj field = getf obj field
let ( .@()<- ) obj field v = setf obj field v

let fields structure name typ n =
  Iarray.init n (fun i ->
      let name = Format.sprintf "%s[%d]" name i in
      field structure name typ )

module Address = struct
  include Chain.Ethereum.Address

  module Repr = struct
    type t
    let t : t structure typ = structure "monad_address"
    let bytes = fields t "byte" char byte_width
    let () = seal t
  end

  let read (repr : Repr.t structure) : t = init (fun i -> repr.@(Iarray.get Repr.bytes i))

  let write (addr : t) : Repr.t structure =
    let repr = Ctypes.make Repr.t in
    iteri (fun i chr -> repr.@(Iarray.get Repr.bytes i) <- chr) addr ;
    repr

  let t = view ~read ~write Repr.t
end

module Byte_view = struct
  module Repr = struct
    type t
    let t : t structure typ = structure "monad_bv"
    let begin_ = field t "begin" (ptr uint8_t)
    let end_ = field t "end" (ptr uint8_t)
    let () = seal t
  end
  type t = Bytes.t

  let read (repr : Repr.t structure) : t =
    let begin_ = repr.@(Repr.begin_) in
    let end_ = repr.@(Repr.end_) in
    let length = ptr_diff begin_ end_ in
    string_from_ptr (coerce (ptr uint8_t) (ptr char) begin_) ~length

  let write (bs : t) : Repr.t structure =
    let arr = CArray.of_string bs in
    let begin_ = coerce (ptr char) (ptr uint8_t) (CArray.start arr) in
    let end_ = begin_ +@ Bytes.length bs in
    let repr = make Repr.t in
    repr.@(Repr.begin_) <- begin_ ;
    repr.@(Repr.end_) <- end_ ;
    repr

  let t = view ~read ~write Repr.t
end

module Code_header = struct
  module Repr = struct
    type t
    let t : t structure typ = structure "monad_rv_code_header"
    let prefix = fields t "prefix" uint8_t 3
    let code_length = fields t "code_length" uint8_t 4
    let () = seal t
  end

  let extension_prefix = Bytes.of_hex_string "ae0001"
  type t = {prefix : Bytes.t; code_length : int}
  let empty = {prefix = extension_prefix; code_length = 0}

  let read (repr : Repr.t structure) =
    let prefix = Bytes.init 3 (fun i -> Char.chr (Unsigned.UInt8.to_int repr.@(Iarray.get Repr.prefix i))) in
    let code_length =
      let bs =
        Stdlib.Bytes.init 4 (fun i -> Char.chr (Unsigned.UInt8.to_int repr.@(Iarray.get Repr.code_length i)))
      in
      Int32.to_int (Stdlib.Bytes.get_int32_le bs 0)
    in
    {prefix; code_length}

  let write ({prefix; code_length} : t) : Repr.t structure =
    assert (Bytes.length prefix = 3) ;
    let repr = make Repr.t in
    Bytes.iteri
      (fun i chr -> repr.@(Iarray.get Repr.prefix i) <- Unsigned.UInt8.of_int (Char.code chr))
      prefix ;
    let bs = Stdlib.Bytes.make 4 '\x00' in
    Stdlib.Bytes.set_int32_le bs 0 (Int32.of_int code_length) ;
    Stdlib.Bytes.iteri
      (fun i chr -> repr.@(Iarray.get Repr.code_length i) <- Unsigned.UInt8.of_int (Char.code chr))
      bs ;
    repr
  let t = view ~read ~write Repr.t
end

module Code_sections = struct
  module Repr = struct
    type t
    let t : t structure typ = structure "monad_rv_code_sections"
    let code_header = field t "code_header" (ptr Code_header.t)
    let db_blob = field t "db_blob" Byte_view.t
    let code_blob = field t "code_blob" Byte_view.t
    let init_blob = field t "init_blob" Byte_view.t
    let () = seal t
  end

  type t = {code_header : Code_header.t; db_blob : Bytes.t; code_blob : Bytes.t; init_blob : Bytes.t}
  let empty =
    {code_header = Code_header.empty; db_blob = Bytes.empty; code_blob = Bytes.empty; init_blob = Bytes.empty}

  let read (repr : Repr.t structure) : t =
    let code_header = !@(repr.@(Repr.code_header)) in
    let db_blob = repr.@(Repr.db_blob) in
    let code_blob = repr.@(Repr.code_blob) in
    let init_blob = repr.@(Repr.init_blob) in
    {code_header; db_blob; code_blob; init_blob}

  let write ({code_header; db_blob; code_blob; init_blob} : t) : Repr.t structure =
    let repr = make Repr.t in
    repr.@(Repr.code_header) <- allocate Code_header.t code_header ;
    repr.@(Repr.db_blob) <- db_blob ;
    repr.@(Repr.code_blob) <- code_blob ;
    repr.@(Repr.init_blob) <- init_blob ;
    repr

  let t = view ~read ~write Repr.t
end

module Validate_result = struct
  module Repr = struct
    type t = Unsigned.UInt32.t
    let t = uint32_t
  end
  type error =
    [ `Unknown
    | `No_prefix
    | `Bad_header
    | `Code_overflow
    | `Points_outside
    | `Invalid_format
    | `Libzstd_err
    | `Has_elf_magic
    | `Has_zstd_magic
    | `Libelf_error
    | `Elf_not_rv64
    | `No_init_fn
    | `No_main_fn ]
  let to_string = function
    | `Unknown -> "Unknown"
    | `No_prefix -> "No_prefix"
    | `Bad_header -> "Bad_header"
    | `Code_overflow -> "Code_overflow"
    | `Points_outside -> "Points_outside"
    | `Invalid_format -> "Invalid_format"
    | `Libzstd_err -> "Libzstd_err"
    | `Has_elf_magic -> "Has_elf_magic"
    | `Has_zstd_magic -> "Has_zstd_magic"
    | `Libelf_error -> "Libelf_error"
    | `Elf_not_rv64 -> "Elf_not_rv64"
    | `No_init_fn -> "No_init_fn"
    | `No_main_fn -> "No_main_fn "

  type t = [`Ok | error]

  let read (repr : Repr.t) : t =
    match Unsigned.UInt32.to_int repr with
    | 0 -> `Unknown
    | 1 -> `No_prefix
    | 2 -> `Bad_header
    | 3 -> `Code_overflow
    | 4 -> `Points_outside
    | 5 -> `Invalid_format
    | 6 -> `Libzstd_err
    | 7 -> `Has_elf_magic
    | 8 -> `Has_zstd_magic
    | 9 -> `Libelf_error
    | 10 -> `Elf_not_rv64
    | 11 -> `No_init_fn
    | 12 -> `No_main_fn
    | 13 -> `Ok
    | _ -> assert false

  let write (t : t) : Repr.t =
    Unsigned.UInt32.of_int
      ( match t with
      | `Unknown -> 0
      | `No_prefix -> 1
      | `Bad_header -> 2
      | `Code_overflow -> 3
      | `Points_outside -> 4
      | `Invalid_format -> 5
      | `Libzstd_err -> 6
      | `Has_elf_magic -> 7
      | `Has_zstd_magic -> 8
      | `Libelf_error -> 9
      | `Elf_not_rv64 -> 10
      | `No_init_fn -> 11
      | `No_main_fn -> 12
      | `Ok -> 13 )

  let t = view ~read ~write Repr.t
end

module Zstd_decomp = struct
  module Repr = struct
    include Opaque ()

    let create = foreign "monad_rv_code_zstd_decomp_create" (ptr t @-> returning int)
    let destroy = foreign "monad_rv_code_zstd_decomp_destroy" (t @-> returning void)
  end

  type t = Repr.t
  let t = Repr.t

  let make () =
    let ptr = allocate t (coerce (ptr void) t null) in
    let exit_code = Repr.create ptr in
    if exit_code <> 0 then (
      Format.eprintf "Zstd_decomp: exit code %d\n" exit_code ;
      exit 1 ) ;
    let result = !@ptr in
    Gc.finalise Repr.destroy result ; result
end

module Code_token = struct
  include B16
  module Repr = struct
    type t
    let t : t structure typ = structure "monad_rv_code_token_t"
    let bytes = fields t "byte" char byte_width
    let () = seal t
  end

  let read (repr : Repr.t structure) : t = init (fun i -> repr.@(Iarray.get Repr.bytes i))

  let write (addr : t) : Repr.t structure =
    let repr = Ctypes.make Repr.t in
    iteri (fun i chr -> repr.@(Iarray.get Repr.bytes i) <- chr) addr ;
    repr

  let t = view ~read ~write Repr.t
end

module Code_cache = struct
  module Repr = struct
    include Opaque ()

    let create = foreign "monad_rv_code_cache_create" (uint8_t @-> ptr t @-> returning int)
    let destroy = foreign "monad_rv_code_cache_destroy" (t @-> returning void)

    let lookup =
      foreign "monad_rv_code_cache_lookup" (t @-> ptr Address.t @-> ptr Code_token.t @-> returning bool)

    let insert_valid =
      foreign "monad_rv_code_cache_insert_valid"
        ( t
        @-> ptr Address.t
        @-> Byte_view.t
        @-> Zstd_decomp.t
        @-> ptr Code_token.t
        @-> returning Validate_result.t )

    let try_insert_new =
      foreign "monad_rv_code_cache_try_insert_new"
        ( t
        @-> ptr Address.t
        @-> Byte_view.t
        @-> ptr Code_sections.t
        @-> bool
        @-> Zstd_decomp.t
        @-> ptr Code_token.t
        @-> returning Validate_result.t )
  end

  type t = Repr.t
  let t = Repr.t

  let make ~log2_size =
    let log2_size = Unsigned.UInt8.of_int (Char.code log2_size) in
    let ptr = allocate Repr.t (coerce (ptr void) Repr.t null) in
    let exit_code = Repr.create log2_size ptr in
    if exit_code <> 0 then (
      Format.eprintf "Code_cache: exit code %d\n" exit_code ;
      exit 1 ) ;
    let result = !@ptr in
    Gc.finalise Repr.destroy result ; result

  let lookup (cache : t) (addr : Address.t) : Code_token.t option =
    let addr = allocate Address.t addr in
    let token_ptr = allocate Code_token.t B16.zeros in
    if Repr.lookup cache addr token_ptr then Some !@token_ptr else None

  let insert_valid (cache : t) (zstd_decomp : Zstd_decomp.t) (addr : Address.t) (code : Bytes.t) :
      (Code_token.t, Validate_result.error) result =
    let addr = allocate Address.t addr in
    let token_ptr = allocate Code_token.t Code_token.zeros in
    let result = Repr.insert_valid cache addr code zstd_decomp token_ptr in
    match result with `Ok -> Ok !@token_ptr | #Validate_result.error as err -> Error err

  let try_insert_new (cache : t) (zstd_decomp : Zstd_decomp.t) (addr : Address.t) (code : Bytes.t) :
      (Code_sections.t * Code_token.t, Validate_result.error) result =
    let addr = allocate Address.t addr in
    let code_sections_ptr = allocate Code_sections.t Code_sections.empty in
    let token_ptr = allocate Code_token.t Code_token.zeros in
    let result = Repr.try_insert_new cache addr code code_sections_ptr false zstd_decomp token_ptr in
    match result with
    | `Ok -> Ok (!@code_sections_ptr, !@token_ptr)
    | #Validate_result.error as err -> Error err
end
