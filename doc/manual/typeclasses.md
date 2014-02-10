# Type classes

## Type classes for Sets and Maps

Sets and Maps require comparison operations in OCaml and Coq.  This is
provided via type classes `SetType` and `MapType`, introduced in
`library/basic_classes.lem`;
the former has a single method `setElemCompare`.
The default OCaml instantiation of `SetType`
is with OCaml's `compare`, but if the user constructs sets of types
containing any tuples, records, or user-defined inductive types, those
types must also have an instance declaration for `SetType` with a
suitable comparison function.  If this is omitted, the default will be
used and there may be a run-time error as the equality test will be
incorrect.  `MapType` uses `SetType` as default implementation.

For example, for a simple inductive type:

    type memory_order = Atomic | NA

one can make it an instance of `SetType` as follows, as here the default OCaml `compare` and the theorem prover equalities will be correct.

    instance (SetType memory_order)
      let setElemCompare = defaultCompare
    end

For a more complex inductive type such as the following, with recursion through a set and pair constructor:

    type tree 'a =
      | Node of set ('a * tree 'a)

one can define an equality function making use of the underlying `setCompareBy` comparison on sets:

    val treeCompare : forall 'a . 
      ('a -> 'a -> ordering) -> (tree 'a) -> (tree 'a) -> ordering
    let rec treeCompare cmpa (Node xs) (Node ys) =  
      setCompareBy (pairCompare cmpa (treeCompare cmpa)) xs ys 

and make the `tree` type constructor instantiate `SetType` as follows:

    instance forall 'a. SetType 'a => (SetType (tree 'a))
      let setElemCompare = treeCompare setElemCompare
    end 

Tuple types up to a certain size are made an instance of `SetType` in `basic_classes.lem`; if one uses sets or maps of wider tuples, they must also be made instances following the same pattern, otherwise Lem will generate incorrect code.



## Other Standard Library Type Classes

The standard library defines several other type classes.   In `library/basic_classes.lem` we have, in addition to `SetType`:

- `Eq`   for equality and inequality
- `Ord`  for total linear orders with comparison operations
- `OrdMaxMin`  extending `Ord` with max and min


In `map.lem` we have `MapKeyType`.


In `num.lem` there are various numeric types and type classes for the operations that they each may or may not support:

- `NumNegate`
- `NumAdd`
- `NumMinus`
- `NumMult`
- `NumPow`
- `NumDivision`
- `NumIntegerDivision`
- `NumRemainder`
- `NumSucc`
- `NumPred` 

In `word.lem` there is a type class `Word` of machine words, bitwise logical operations, and conversions to and from lists of booleans. 

