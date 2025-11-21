module Impl : sig
  type t = private Bytes.t

  val zeros : t
  val init : char -> t
  val make : (int -> char) -> t
end = struct
  type t = Bytes.t

  let length = 256

  let zeros : t = Bytes.make length '\x00'
  let init c : t = Bytes.make length c
  let make b_i : t = Bytes.init length b_i
end

include Impl
