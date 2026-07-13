type ('a, 'b) t = {
    get : 'a -> 'b;
    set : 'b -> 'a -> 'a
  }

let modify l f x = l.set (f (l.get x)) x

module Infix = struct
  let (|--) l1 l2 =
    { get = (fun s -> l2.get (l1.get s))
    ; set = (fun v s ->
      l1.set (l2.set v (l1.get s)) s)
    }
end
