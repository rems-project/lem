module QI = Rational_impl.QI

type t = QI.t

let of_int = QI.of_int
let of_ints = QI.of_ints
let of_big_int = QI.of_big_int

let add = QI.add
let sub = QI.sub
let mul = QI.mul
let div = QI.div
let neg = QI.neg
let abs = QI.abs

let equal = QI.equal
let lt = QI.lt
let gt = QI.gt
let leq = QI.leq
let geq = QI.geq

let min = QI.min
let max = QI.max

let floor = QI.floor
let ceiling = QI.ceiling

let num = QI.num
let den = QI.den
