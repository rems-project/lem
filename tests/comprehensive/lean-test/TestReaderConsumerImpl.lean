/- Hand-written implementation for test_reader_consumer.lem's consumer
   val (`declare {lean} reader_consumer val scaled`): the reader
   parameters arrive as explicit LEADING arguments, in the global
   sorted reader order, before the val's own arguments — exactly what
   the backend emits at every call site. -/

namespace TestReaderConsumerImpl

def scaled (cfg : Nat) (x : Nat) : Nat := cfg * 100 + x

end TestReaderConsumerImpl
