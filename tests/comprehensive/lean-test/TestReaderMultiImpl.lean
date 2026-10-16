/- Hand-written implementation for test_reader_multi.lem's consumer val
   (`declare {lean} reader_consumer val combine`; N-ary reader_seed
   slice, 2026-09-19): the THREE reader parameters arrive as explicit
   LEADING arguments in the global sorted reader order — alpha, beta,
   gamma (NOT the .lem declaration order gamma, alpha, beta) — before
   the val's own argument; exactly what the backend emits at every call
   site. alpha and gamma share a type, so the value below is what makes
   a positional swap observable (alpha weighs 1000, gamma weighs 10). -/

namespace TestReaderMultiImpl

def combine (alpha : Nat) (beta : String) (gamma : Nat) (x : Nat) : Nat :=
  alpha * 1000 + beta.length * 100 + gamma * 10 + x

end TestReaderMultiImpl
