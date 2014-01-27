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

let gen_pow (one : 'a) (mul : 'a -> 'a -> 'a) (b : 'a) (e : int) : 'a = 
  let rec aux (a : 'a) (b : 'a) (e : int) =
     if e = 1 then (mul a b) else
      let e' = e / 2 in
      let a' = (if (e mod 2) = 0 then a else mul a b) in
      aux a' (mul b b) e'
  in     
  if e < 0 then raise (Failure "negative exponent") else 
  if (e = 0) then one else aux one b e

let nat_pow b e = gen_pow 1 (fun a b -> a * b) b e;;
let int_pow b e = nat_pow b e;;
let int32_pow (b : int32) e = gen_pow Int32.one Int32.mul b e
 
let int_mod i n = 
  let r = i mod n in
  if (r < 0) then r + n else r

let int_div i n = 
  let r = i / n in
  if (i mod n < 0) then r - 1 else r

let int32_mod i n = 
  let r = Int32.rem i n in
  if (r < Int32.zero) then Int32.add r n else r

let int32_div i n = 
  let r = Int32.div i n in
  if (Int32.rem i n < Int32.zero) then Int32.pred r else r

