type nat = int
type natural = Big_int.big_int

let nat_monus x y =
  let d = x - y in
    if d < 0 then
      0
    else
      d

let natural_monus x y =
    (if Big_int.le_big_int x y then
      Big_int.zero_big_int
    else
      (Big_int.sub_big_int x y))

let nat_pred x = nat_monus x 1
let natural_pred x = natural_monus x Big_int.unit_big_int

let nat_pow b e = 
  let rec aux a b e =
     if e = 1 then (a * b) else
      let e' = e / 2 in
      let a' = (if (e mod 2) = 0 then a else (a * b)) in
      aux a' (b * b) e'
  in     
  if e < 0 then raise (Failure "negative exponent") else 
  if (e = 0) then 1 else aux 1 b e

let int_pow b e = nat_pow b e;;
 
let int_mod i n = 
  let r = i mod n in
  if (r < 0) then r + n else r

let int_div i n = 
  let r = i / n in
  if (i mod n < 0) then r - 1 else r
