module QI = struct
  type t = Num.num

  let of_int = Num.num_of_int
  let of_ints x y = Num.div_num (of_int x) (of_int y)

  let add = Num.add_num
  let sub = Num.sub_num
  let mul = Num.mult_num
  let div = Num.div_num
  let neg = Num.minus_num
  let abs = Num.abs_num

  let equal = Num.eq_num
  let lt = Num.lt_num
  let gt = Num.gt_num
  let leq = Num.le_num
  let geq = Num.ge_num
  let min = Num.min_num
  let max = Num.max_num
end
