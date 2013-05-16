type num = int
let (<) = (<)
let (<=) = (<=)
let (>) = (>)
let (>=) = (>=)
let (+) = (+)
let (-) x y =
  let d = x - y in
    if d < 0 then
      0
    else
      d
let ( * ) = ( * )
let (/) = (/)
let (mod) = (mod)
let (land) = (land)
let (lor) = (lor)
let (lxor) = (lxor)
let lnot = lnot
let (lsl) = (lsl)
let (lsr) = (lsr)
let (asr) = (asr)
let num_of_string n = int_of_string n
let string_of_num n = string_of_int n
let int i = i
let neg i = -i

let exp b e = 
  let rec aux a b e =
     if e = 1 then (a * b) else
      let e' = e / 2 in
      let a' = (if (e mod 2) = 0 then a else (a * b)) in
      aux a' (b * b) e'
  in     
  if e < 0 then raise (Failure "negative exponent") else 
  if (e = 0) then 1 else aux 1 b e

let int_exp = exp
