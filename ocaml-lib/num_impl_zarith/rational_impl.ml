module QI = struct
  include Q
  let floor x = Z.fdiv (num x) (den x)
  let ceiling x = Z.cdiv (num x) (den x)
  let of_big_int = of_bigint
end
