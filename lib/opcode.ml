type t =
  (* 0x0X *)
  | Stop
  | Add
  | Mul
  | Sub
  | Udiv
  | Sdiv
  | Umod
  | Smod
  | Addmod
  | Mulmod
  | Exp
  | Signextend
  (* 0x1X *)
  | Lt
  | Gt
  | Slt
  | Sgt
  | Eq
  | Iszero
  | And
  | Or
  | Xor
  | Not
  | Byte
  | Shl
  | Shr
  | Sar
  (* 0x2X *)
  | Keccak
  (* 0x3X *)
  | Address
  | Balance
  | Origin
  | Caller
  | Callvalue
  | Calldataload
  | Calldatasize
  | Calldatacopy
  | Codesize
  | Codecopy
  | Gasprice
  | Extcodesize
  | Extcodecopy
  | Returndatasize
  | Returndatacopy
  | Extcodehash
  (* 0x4X *)
  | Blockhash
  | Coinbase
  | Timestamp
  | Number
  | Prevrandao
  | Gaslimit
  | Chainid
  | Selfbalance
  | Basefee
  | Blobhash
  | Blobbasefee
  (* 0x5X *)
  | Pop
  | Mload
  | Mstore
  | Mstore8
  | Sload
  | Sstore
  | Jump
  | Jumpi
  | Pc
  | Msize
  | Gas
  | Jumpdest
  | Tload
  | Tstore
  | Mcopy
  | Push of int
  (* 0x8X*)
  | Dup of int
  (* 0x9X *)
  | Swap of int
  (* 0xAX *)
  | Log of int
  (* 0xFX *)
  | Create
  | Call
  | Callcode
  | Return
  | Delegatecall
  | Create2
  | Staticcall
  | Revert
  | Invalid
  | Selfdestruct
  | Undefined of char

type info = {opcode : t; byte : char; name : string}

let of_byte = function
  | '\x00' -> Stop
  | '\x01' -> Add
  | '\x02' -> Mul
  | '\x03' -> Sub
  | '\x04' -> Udiv
  | '\x05' -> Sdiv
  | '\x06' -> Umod
  | '\x07' -> Smod
  | '\x08' -> Addmod
  | '\x09' -> Mulmod
  | '\x0A' -> Exp
  | '\x0B' -> Signextend
  | '\x10' -> Lt
  | '\x11' -> Gt
  | '\x12' -> Slt
  | '\x13' -> Sgt
  | '\x14' -> Eq
  | '\x15' -> Iszero
  | '\x16' -> And
  | '\x17' -> Or
  | '\x18' -> Xor
  | '\x19' -> Not
  | '\x1A' -> Byte
  | '\x1b' -> Shl
  | '\x1c' -> Shr
  | '\x1d' -> Sar
  | '\x20' -> Keccak
  | '\x30' -> Address
  | '\x31' -> Balance
  | '\x32' -> Origin
  | '\x33' -> Caller
  | '\x34' -> Callvalue
  | '\x35' -> Calldataload
  | '\x36' -> Calldatasize
  | '\x37' -> Calldatacopy
  | '\x38' -> Codesize
  | '\x39' -> Codecopy
  | '\x3a' -> Gasprice
  | '\x3b' -> Extcodesize
  | '\x3c' -> Extcodecopy
  | '\x3d' -> Returndatasize
  | '\x3e' -> Returndatacopy
  | '\x3f' -> Extcodehash
  | '\x40' -> Blockhash
  | '\x41' -> Coinbase
  | '\x42' -> Timestamp
  | '\x43' -> Number
  | '\x44' -> Prevrandao
  | '\x45' -> Gaslimit
  | '\x46' -> Chainid
  | '\x47' -> Selfbalance
  | '\x48' -> Basefee
  | '\x49' -> Blobhash
  | '\x4a' -> Blobbasefee
  | '\x50' -> Pop
  | '\x51' -> Mload
  | '\x52' -> Mstore
  | '\x53' -> Mstore8
  | '\x54' -> Sload
  | '\x55' -> Sstore
  | '\x56' -> Jump
  | '\x57' -> Jumpi
  | '\x58' -> Pc
  | '\x59' -> Msize
  | '\x5a' -> Gas
  | '\x5b' -> Jumpdest
  | '\x5c' -> Tload
  | '\x5d' -> Tstore
  | '\x5e' -> Mcopy
  | '\x5f' -> Push 0
  | '\x60' .. '\x7f' as opcode -> Push (Char.code opcode - 0x60 + 1)
  | '\x80' .. '\x8f' as opcode -> Dup (Char.code opcode - 0x80 + 1)
  | '\x90' .. '\x9f' as opcode -> Swap (Char.code opcode - 0x90 + 1)
  | '\xa0' .. '\xa4' as opcode -> Log (Char.code opcode - 0xa0)
  | '\xf0' -> Create
  | '\xf1' -> Call
  | '\xf2' -> Callcode
  | '\xf3' -> Return
  | '\xf4' -> Delegatecall
  | '\xf5' -> Create2
  | '\xfa' -> Staticcall
  | '\xfd' -> Revert
  | '\xfe' -> Invalid
  | '\xff' -> Selfdestruct
  | opcode -> Undefined opcode

let info = function
  | Stop -> {opcode = Stop; byte = '\x00'; name = "STOP"}
  | Add -> {opcode = Add; byte = '\x01'; name = "ADD"}
  | Mul -> {opcode = Mul; byte = '\x02'; name = "MUL"}
  | Sub -> {opcode = Sub; byte = '\x03'; name = "SUB"}
  | Udiv -> {opcode = Udiv; byte = '\x04'; name = "UDIV"}
  | Sdiv -> {opcode = Sdiv; byte = '\x05'; name = "SDIV"}
  | Umod -> {opcode = Umod; byte = '\x06'; name = "UMOD"}
  | Smod -> {opcode = Smod; byte = '\x07'; name = "SMOD"}
  | Addmod -> {opcode = Addmod; byte = '\x08'; name = "ADDMOD"}
  | Mulmod -> {opcode = Mulmod; byte = '\x09'; name = "MULMOD"}
  | Exp -> {opcode = Exp; byte = '\x0A'; name = "EXP"}
  | Signextend -> {opcode = Signextend; byte = '\x0B'; name = "SIGNEXTEND"}
  | Lt -> {opcode = Lt; byte = '\x10'; name = "LT"}
  | Gt -> {opcode = Gt; byte = '\x11'; name = "GT"}
  | Slt -> {opcode = Slt; byte = '\x12'; name = "SLT"}
  | Sgt -> {opcode = Sgt; byte = '\x13'; name = "SGT"}
  | Eq -> {opcode = Eq; byte = '\x14'; name = "EQ"}
  | Iszero -> {opcode = Iszero; byte = '\x15'; name = "ISZERO"}
  | And -> {opcode = And; byte = '\x16'; name = "AND"}
  | Or -> {opcode = Or; byte = '\x17'; name = "OR"}
  | Xor -> {opcode = Xor; byte = '\x18'; name = "XOR"}
  | Not -> {opcode = Not; byte = '\x19'; name = "NOT"}
  | Byte -> {opcode = Byte; byte = '\x1A'; name = "BYTE"}
  | Shl -> {opcode = Shl; byte = '\x1b'; name = "SHL"}
  | Shr -> {opcode = Shr; byte = '\x1c'; name = "SHR"}
  | Sar -> {opcode = Sar; byte = '\x1d'; name = "SAR"}
  | Keccak -> {opcode = Keccak; byte = '\x20'; name = "KECCAK"}
  | Address -> {opcode = Address; byte = '\x30'; name = "ADDRESS"}
  | Balance -> {opcode = Balance; byte = '\x31'; name = "BALANCE"}
  | Origin -> {opcode = Origin; byte = '\x32'; name = "ORIGIN"}
  | Caller -> {opcode = Caller; byte = '\x33'; name = "CALLER"}
  | Callvalue -> {opcode = Callvalue; byte = '\x34'; name = "CALLVALUE"}
  | Calldataload -> {opcode = Calldataload; byte = '\x35'; name = "CALLDATALOAD"}
  | Calldatasize -> {opcode = Calldatasize; byte = '\x36'; name = "CALLDATASIZE"}
  | Calldatacopy -> {opcode = Calldatacopy; byte = '\x37'; name = "CALLDATACOPY"}
  | Codesize -> {opcode = Codesize; byte = '\x38'; name = "CODESIZE"}
  | Codecopy -> {opcode = Codecopy; byte = '\x39'; name = "CODECOPY"}
  | Gasprice -> {opcode = Gasprice; byte = '\x3a'; name = "GASPRICE"}
  | Extcodesize -> {opcode = Extcodesize; byte = '\x3b'; name = "EXTCODESIZE"}
  | Extcodecopy -> {opcode = Extcodecopy; byte = '\x3c'; name = "EXTCODECOPY"}
  | Returndatasize -> {opcode = Returndatasize; byte = '\x3d'; name = "RETURNDATASIZE"}
  | Returndatacopy -> {opcode = Returndatacopy; byte = '\x3e'; name = "RETURNDATACOPY"}
  | Extcodehash -> {opcode = Extcodehash; byte = '\x3f'; name = "EXTCODEHASH"}
  | Blockhash -> {opcode = Blockhash; byte = '\x40'; name = "BLOCKHASH"}
  | Coinbase -> {opcode = Coinbase; byte = '\x41'; name = "COINBASE"}
  | Timestamp -> {opcode = Timestamp; byte = '\x42'; name = "TIMESTAMP"}
  | Number -> {opcode = Number; byte = '\x43'; name = "NUMBER"}
  | Prevrandao -> {opcode = Prevrandao; byte = '\x44'; name = "PREVRANDAO"}
  | Gaslimit -> {opcode = Gaslimit; byte = '\x45'; name = "GASLIMIT"}
  | Chainid -> {opcode = Chainid; byte = '\x46'; name = "CHAINID"}
  | Selfbalance -> {opcode = Selfbalance; byte = '\x47'; name = "SELFBALANCE"}
  | Basefee -> {opcode = Basefee; byte = '\x48'; name = "BASEFEE"}
  | Blobhash -> {opcode = Blobhash; byte = '\x49'; name = "BLOBHASH"}
  | Blobbasefee -> {opcode = Blobbasefee; byte = '\x4a'; name = "BLOBBASEFEE"}
  | Pop -> {opcode = Pop; byte = '\x50'; name = "POP"}
  | Mload -> {opcode = Mload; byte = '\x51'; name = "MLOAD"}
  | Mstore -> {opcode = Mstore; byte = '\x52'; name = "MSTORE"}
  | Mstore8 -> {opcode = Mstore8; byte = '\x53'; name = "MSTORE8"}
  | Sload -> {opcode = Sload; byte = '\x54'; name = "SLOAD"}
  | Sstore -> {opcode = Sstore; byte = '\x55'; name = "SSTORE"}
  | Jump -> {opcode = Jump; byte = '\x56'; name = "JUMP"}
  | Jumpi -> {opcode = Jumpi; byte = '\x57'; name = "JUMPI"}
  | Pc -> {opcode = Pc; byte = '\x58'; name = "PC"}
  | Msize -> {opcode = Msize; byte = '\x59'; name = "MSIZE"}
  | Gas -> {opcode = Gas; byte = '\x5a'; name = "GAS"}
  | Jumpdest -> {opcode = Jumpdest; byte = '\x5b'; name = "JUMPDEST"}
  | Tload -> {opcode = Tload; byte = '\x5c'; name = "TLOAD"}
  | Tstore -> {opcode = Tstore; byte = '\x5d'; name = "TSTORE"}
  | Mcopy -> {opcode = Mcopy; byte = '\x5e'; name = "MCOPY"}
  | Push 0 -> {opcode = Push 0; byte = '\x5f'; name = "PUSH0"}
  | Push i -> {opcode = Push i; byte = Char.chr (0x60 + i - 1); name = Format.sprintf "PUSH%d" i}
  | Dup i -> {opcode = Dup i; byte = Char.chr (0x80 + i - 1); name = Format.sprintf "DUP%d" i}
  | Swap i -> {opcode = Swap i; byte = Char.chr (0x90 + i - 1); name = Format.sprintf "SWAP%d" i}
  | Log i -> {opcode = Log i; byte = Char.chr (0xa0 + i); name = Format.sprintf "LOG%d" i}
  | Create -> {opcode = Create; byte = '\xf0'; name = "CREATE"}
  | Call -> {opcode = Call; byte = '\xf1'; name = "CALL"}
  | Callcode -> {opcode = Callcode; byte = '\xf2'; name = "CALLCODE"}
  | Return -> {opcode = Return; byte = '\xf3'; name = "RETURN"}
  | Delegatecall -> {opcode = Delegatecall; byte = '\xf4'; name = "DELEGATECALL"}
  | Create2 -> {opcode = Create2; byte = '\xf5'; name = "CREATE2"}
  | Staticcall -> {opcode = Staticcall; byte = '\xfa'; name = "STATICCALL"}
  | Revert -> {opcode = Revert; byte = '\xfd'; name = "REVERT"}
  | Invalid -> {opcode = Invalid; byte = '\xfe'; name = "INVALID"}
  | Selfdestruct -> {opcode = Selfdestruct; byte = '\xff'; name = "SELFDESTRUCT"}
  | Undefined opcode ->
      {opcode = Undefined opcode; byte = opcode; name = Format.sprintf "Undefined(0x%x)" (Char.code opcode)}

let to_byte opcode = (info opcode).byte
let to_bytes opcode = Byte_string.Bytes.of_char (to_byte opcode)

let to_string opcode = (info opcode).name
