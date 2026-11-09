let () =
  Printf.printf "wrapped = %d\nwrapped >= 0 = %b\n2 ** 64 = %d\nint_wrap = %d\n"
    Nat63.wrapped Nat63.wrapped_is_zero_or_more Nat63.pow_wrap Nat63.int_wrap
