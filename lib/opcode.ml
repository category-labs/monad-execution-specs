type t =
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
  | Keccak
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
  | Dup of int
  | Swap of int
  | Log of int
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
  | Stop -> {opcode = Stop; byte = '\x00'; name = "Stop"}
  | Add -> {opcode = Add; byte = '\x01'; name = "Add"}
  | Mul -> {opcode = Mul; byte = '\x02'; name = "Mul"}
  | Sub -> {opcode = Sub; byte = '\x03'; name = "Sub"}
  | Udiv -> {opcode = Udiv; byte = '\x04'; name = "Udiv"}
  | Sdiv -> {opcode = Sdiv; byte = '\x05'; name = "Sdiv"}
  | Umod -> {opcode = Umod; byte = '\x06'; name = "Umod"}
  | Smod -> {opcode = Smod; byte = '\x07'; name = "Smod"}
  | Addmod -> {opcode = Addmod; byte = '\x08'; name = "Addmod"}
  | Mulmod -> {opcode = Mulmod; byte = '\x09'; name = "Mulmod"}
  | Exp -> {opcode = Exp; byte = '\x0A'; name = "Exp"}
  | Signextend -> {opcode = Signextend; byte = '\x0B'; name = "Signextend"}
  | Lt -> {opcode = Lt; byte = '\x10'; name = "Lt"}
  | Gt -> {opcode = Gt; byte = '\x11'; name = "Gt"}
  | Slt -> {opcode = Slt; byte = '\x12'; name = "Slt"}
  | Sgt -> {opcode = Sgt; byte = '\x13'; name = "Sgt"}
  | Eq -> {opcode = Eq; byte = '\x14'; name = "Eq"}
  | Iszero -> {opcode = Iszero; byte = '\x15'; name = "Iszero"}
  | And -> {opcode = And; byte = '\x16'; name = "And"}
  | Or -> {opcode = Or; byte = '\x17'; name = "Or"}
  | Xor -> {opcode = Xor; byte = '\x18'; name = "Xor"}
  | Not -> {opcode = Not; byte = '\x19'; name = "Not"}
  | Byte -> {opcode = Byte; byte = '\x1A'; name = "Byte"}
  | Shl -> {opcode = Shl; byte = '\x1b'; name = "Shl"}
  | Shr -> {opcode = Shr; byte = '\x1c'; name = "Shr"}
  | Sar -> {opcode = Sar; byte = '\x1d'; name = "Sar"}
  | Keccak -> {opcode = Keccak; byte = '\x20'; name = "Keccak"}
  | Address -> {opcode = Address; byte = '\x30'; name = "Address"}
  | Balance -> {opcode = Balance; byte = '\x31'; name = "Balance"}
  | Origin -> {opcode = Origin; byte = '\x32'; name = "Origin"}
  | Caller -> {opcode = Caller; byte = '\x33'; name = "Caller"}
  | Callvalue -> {opcode = Callvalue; byte = '\x34'; name = "Callvalue"}
  | Calldataload -> {opcode = Calldataload; byte = '\x35'; name = "Calldataload"}
  | Calldatasize -> {opcode = Calldatasize; byte = '\x36'; name = "Calldatasize"}
  | Calldatacopy -> {opcode = Calldatacopy; byte = '\x37'; name = "Calldatacopy"}
  | Codesize -> {opcode = Codesize; byte = '\x38'; name = "Codesize"}
  | Codecopy -> {opcode = Codecopy; byte = '\x39'; name = "Codecopy"}
  | Gasprice -> {opcode = Gasprice; byte = '\x3a'; name = "Gasprice"}
  | Extcodesize -> {opcode = Extcodesize; byte = '\x3b'; name = "Extcodesize"}
  | Extcodecopy -> {opcode = Extcodecopy; byte = '\x3c'; name = "Extcodecopy"}
  | Returndatasize -> {opcode = Returndatasize; byte = '\x3d'; name = "Returndatasize"}
  | Returndatacopy -> {opcode = Returndatacopy; byte = '\x3e'; name = "Returndatacopy"}
  | Extcodehash -> {opcode = Extcodehash; byte = '\x3f'; name = "Extcodehash"}
  | Blockhash -> {opcode = Blockhash; byte = '\x40'; name = "Blockhash"}
  | Coinbase -> {opcode = Coinbase; byte = '\x41'; name = "Coinbase"}
  | Timestamp -> {opcode = Timestamp; byte = '\x42'; name = "Timestamp"}
  | Number -> {opcode = Number; byte = '\x43'; name = "Number"}
  | Prevrandao -> {opcode = Prevrandao; byte = '\x44'; name = "Prevrandao"}
  | Gaslimit -> {opcode = Gaslimit; byte = '\x45'; name = "Gaslimit"}
  | Chainid -> {opcode = Chainid; byte = '\x46'; name = "Chainid"}
  | Selfbalance -> {opcode = Selfbalance; byte = '\x47'; name = "Selfbalance"}
  | Basefee -> {opcode = Basefee; byte = '\x48'; name = "Basefee"}
  | Blobhash -> {opcode = Blobhash; byte = '\x49'; name = "Blobhash"}
  | Blobbasefee -> {opcode = Blobbasefee; byte = '\x4a'; name = "Blobbasefee"}
  | Pop -> {opcode = Pop; byte = '\x50'; name = "Pop"}
  | Mload -> {opcode = Mload; byte = '\x51'; name = "Mload"}
  | Mstore -> {opcode = Mstore; byte = '\x52'; name = "Mstore"}
  | Mstore8 -> {opcode = Mstore8; byte = '\x53'; name = "Mstore8"}
  | Sload -> {opcode = Sload; byte = '\x54'; name = "Sload"}
  | Sstore -> {opcode = Sstore; byte = '\x55'; name = "Sstore"}
  | Jump -> {opcode = Jump; byte = '\x56'; name = "Jump"}
  | Jumpi -> {opcode = Jumpi; byte = '\x57'; name = "Jumpi"}
  | Pc -> {opcode = Pc; byte = '\x58'; name = "Pc"}
  | Msize -> {opcode = Msize; byte = '\x59'; name = "Msize"}
  | Gas -> {opcode = Gas; byte = '\x5a'; name = "Gas"}
  | Jumpdest -> {opcode = Jumpdest; byte = '\x5b'; name = "Jumpdest"}
  | Tload -> {opcode = Tload; byte = '\x5c'; name = "Tload"}
  | Tstore -> {opcode = Tstore; byte = '\x5d'; name = "Tstore"}
  | Mcopy -> {opcode = Mcopy; byte = '\x5e'; name = "Mcopy"}
  | Push 0 -> {opcode = Push 0; byte = '\x5f'; name = "Push0"}
  | Push i -> {opcode = Push i; byte = Char.chr (0x60 + i - 1); name = Format.sprintf "Push%d" i}
  | Dup i -> {opcode = Dup i; byte = Char.chr (0x80 + i - 1); name = Format.sprintf "Dup%d" i}
  | Swap i -> {opcode = Swap i; byte = Char.chr (0x90 + i - 1); name = Format.sprintf "Swap%d" i}
  | Log i -> {opcode = Log i; byte = Char.chr (0xa0 + i); name = Format.sprintf "Log%d" i}
  | Create -> {opcode = Create; byte = '\xf0'; name = "Create"}
  | Call -> {opcode = Call; byte = '\xf1'; name = "Call"}
  | Callcode -> {opcode = Callcode; byte = '\xf2'; name = "Callcode"}
  | Return -> {opcode = Return; byte = '\xf3'; name = "Return"}
  | Delegatecall -> {opcode = Delegatecall; byte = '\xf4'; name = "Delegatecall"}
  | Create2 -> {opcode = Create2; byte = '\xf5'; name = "Create2"}
  | Staticcall -> {opcode = Staticcall; byte = '\xfa'; name = "Staticcall"}
  | Revert -> {opcode = Revert; byte = '\xfd'; name = "Revert"}
  | Invalid -> {opcode = Invalid; byte = '\xfe'; name = "Invalid"}
  | Selfdestruct -> {opcode = Selfdestruct; byte = '\xff'; name = "Selfdestruct"}
  | Undefined opcode ->
      {opcode = Undefined opcode; byte = opcode; name = Format.sprintf "Undefined(0x%x)" (Char.code opcode)}

let to_byte opcode = (info opcode).byte

let to_string opcode = (info opcode).name
