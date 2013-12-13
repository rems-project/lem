# Typeclasses

## Type-classes for Sets and Maps
- Sets and Maps require comparison operation in OCaml and Coq
- `SetType` and `MapType` used to provide this comparison function
- default instantiation of `SetType` is by OCaml's `compare`
- for types, where this fails user needs to provide instantion, otherwise OCaml run-time error
- `MapType` uses `SetType` as default implementation

