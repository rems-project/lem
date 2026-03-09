/-!
# LemLib — Lean 4 runtime library for Lem

Provides the core types and operations that Lem-generated Lean 4 code depends on:
- `DAEMON`: undefined value axiom (analogous to Coq's DAEMON)
- `LemOrdering`: three-way comparison type used by set/map operations
- Comparison, arithmetic, and string helpers
- Set operations (using sorted `List` representation with `LemOrdering` comparators)
- Finite map operations (using `List (α × β)` with `LemOrdering` comparators)

**Convention**: Functions suffixed with `By` take an explicit `(cmp : α → α → LemOrdering)`
comparator. Functions without `By` use Lean's `BEq` or `Ord` type classes.
-/

/- Lem standard library support for Lean 4 -/

/- DAEMON: undefined value placeholder, analogous to Coq's DAEMON axiom -/
axiom DAEMON : ∀ {α : Type}, α

/- Lem uses lowercase 'vector' for its built-in vector type -/
abbrev vector (α : Type) (n : Nat) := Vector α n

/- Ordering type for comparisons -/
inductive LemOrdering where
  | LT : LemOrdering
  | EQ : LemOrdering
  | GT : LemOrdering
  deriving Repr, BEq, Inhabited, DecidableEq

/- Ordering predicates -/
def isLess (o : LemOrdering) : Bool := o == .LT
def isLessEqual (o : LemOrdering) : Bool := o != .GT
def isGreater (o : LemOrdering) : Bool := o == .GT
def isGreaterEqual (o : LemOrdering) : Bool := o != .LT

/- Ord instance for Prod (not in Lean stdlib) -/
instance [Ord α] [Ord β] : Ord (α × β) where
  compare p q :=
    match compare p.1 q.1 with
    | .lt => .lt
    | .gt => .gt
    | .eq => compare p.2 q.2

/- Default comparison via Ord -/
def defaultCompare [Ord α] (x y : α) : LemOrdering :=
  match compare x y with
  | .lt => .LT
  | .eq => .EQ
  | .gt => .GT

def defaultLess [Ord α] (x y : α) : Bool := isLess (defaultCompare x y)
def defaultLessEq [Ord α] (x y : α) : Bool := isLessEqual (defaultCompare x y)
def defaultGreater [Ord α] (x y : α) : Bool := isGreater (defaultCompare x y)
def defaultGreaterEq [Ord α] (x y : α) : Bool := isGreaterEqual (defaultCompare x y)

/- Bool/Prop bridge -/
def lemBoolToProp (b : Bool) : Prop := b = true

/- failwith: raises a panic with the given message -/
unsafe def failwithImpl {α : Type} (msg : String) : α :=
  @panic α ⟨unsafeCast ()⟩ msg

@[implemented_by failwithImpl]
def failwith {α : Type} (_msg : String) : α := DAEMON

/- Function application -/
def apply (f : α → β) (x : α) : β := f x

/- List operations -/
def listEqualBy (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => eq x y && listEqualBy eq xs ys
  | _, _ => false

def listMemberBy (eq : α → α → Bool) (x : α) : List α → Bool
  | [] => false
  | y :: ys => eq x y || listMemberBy eq x ys

/- Tuple equality -/
def tupleEqualBy (eq1 : α → α → Bool) (eq2 : β → β → Bool) (p1 : α × β) (p2 : α × β) : Bool :=
  eq1 p1.1 p2.1 && eq2 p1.2 p2.2

/- Natural number operations -/
@[inline] def natPower (base exp : Nat) : Nat := base ^ exp
@[inline] def natDiv (a b : Nat) : Nat := a / b
@[inline] def natMod (a b : Nat) : Nat := a % b
@[inline] def natMin (a b : Nat) : Nat := min a b
@[inline] def natMax (a b : Nat) : Nat := max a b
@[inline] def natLtb (a b : Nat) : Bool := a < b
@[inline] def natLteb (a b : Nat) : Bool := a ≤ b
@[inline] def natGtb (a b : Nat) : Bool := a > b
@[inline] def natGteb (a b : Nat) : Bool := a ≥ b

/- Exponentiation by squaring -/
def gen_pow_aux (mul : α → α → α) (one : α) (base : α) (exp : Nat) : α :=
  match exp with
  | 0 => one
  | 1 => mul one base
  | n + 2 =>
    let half := (n + 2) / 2
    let one' := if (n + 2) % 2 == 0 then one else mul one base
    gen_pow_aux mul one' (mul base base) half
termination_by exp
decreasing_by omega

/- Integer operations -/
@[inline] def intLtb (a b : Int) : Bool := a < b
@[inline] def intLteb (a b : Int) : Bool := a ≤ b
@[inline] def intGtb (a b : Int) : Bool := a > b
@[inline] def intGteb (a b : Int) : Bool := a ≥ b

/- String operations -/
def stringMakeString (n : Nat) (c : Char) : String := String.ofList (List.replicate n c)

/- Sorting by LemOrdering comparison -/
def sort_by_ordering (cmp : α → α → LemOrdering) (l : List α) : List α :=
  let leanCmp : α → α → Bool := fun a b => match cmp a b with
    | .LT => true
    | .EQ => true
    | .GT => false
  l.mergeSort leanCmp

/- Set operations (using List as a simple set representation) -/
def setEmpty : List α := []
@[inline] def setIsEmpty : List α → Bool := List.isEmpty
def setSingleton (x : α) : List α := [x]

def setAdd [BEq α] (x : α) (s : List α) : List α :=
  if s.elem x then s else x :: s

def setMemberBy (cmp : α → α → LemOrdering) (x : α) (s : List α) : Bool :=
  match s with
  | [] => false
  | y :: ys => match cmp x y with
    | .EQ => true
    | _ => setMemberBy cmp x ys

@[inline] def setCardinal : List α → Nat := List.length

def setFromList [BEq α] (l : List α) : List α :=
  l.foldr (fun x acc => if acc.elem x then acc else x :: acc) []

def setFromListBy (cmp : α → α → LemOrdering) (l : List α) : List α :=
  l.foldr (fun x acc => if setMemberBy cmp x acc then acc else x :: acc) []

@[inline] def setToList (s : List α) : List α := s

def setEqualBy (cmp : α → α → LemOrdering) (s1 s2 : List α) : Bool :=
  s1.length == s2.length &&
  s1.all (fun x => setMemberBy cmp x s2) &&
  s2.all (fun x => setMemberBy cmp x s1)

private def sortedCompareBy (cmp : α → α → LemOrdering) : List α → List α → LemOrdering
  | [], [] => .EQ
  | [], _ :: _ => .LT
  | _ :: _, [] => .GT
  | x :: xs, y :: ys => match cmp x y with
    | .LT => .LT
    | .GT => .GT
    | .EQ => sortedCompareBy cmp xs ys

def setCompareBy (cmp : α → α → LemOrdering) (s1 s2 : List α) : LemOrdering :=
  sortedCompareBy cmp (sort_by_ordering cmp s1) (sort_by_ordering cmp s2)

def setUnionBy (cmp : α → α → LemOrdering) (s1 s2 : List α) : List α :=
  match s1 with
  | [] => s2
  | x :: xs =>
    if setMemberBy cmp x s2 then
      setUnionBy cmp xs s2
    else
      x :: setUnionBy cmp xs s2

def setInterBy (cmp : α → α → LemOrdering) (s1 s2 : List α) : List α :=
  match s1 with
  | [] => []
  | x :: xs =>
    if setMemberBy cmp x s2 then
      x :: setInterBy cmp xs s2
    else
      setInterBy cmp xs s2

def setDiffBy (cmp : α → α → LemOrdering) (s1 s2 : List α) : List α :=
  match s1 with
  | [] => []
  | x :: xs =>
    if setMemberBy cmp x s2 then
      setDiffBy cmp xs s2
    else
      x :: setDiffBy cmp xs s2

def setSubsetBy (cmp : α → α → LemOrdering) (s1 s2 : List α) : Bool :=
  match s1 with
  | [] => true
  | x :: xs =>
    if setMemberBy cmp x s2 then
      setSubsetBy cmp xs s2
    else
      false

def setProperSubsetBy (cmp : α → α → LemOrdering) (s1 s2 : List α) : Bool :=
  setSubsetBy cmp s1 s2 && !(setEqualBy cmp s1 s2)

def setSigmaBy (_cmp : α → α → LemOrdering) (s : List α) (f : α → List β) : List (α × β) :=
  s.foldl (fun acc x => acc ++ (f x).map (fun y => (x, y))) []

@[inline] def setAny (f : α → Bool) (s : List α) : Bool := s.any f
@[inline] def setForAll (f : α → Bool) (s : List α) : Bool := s.all f
def setFold (f : α → β → β) (s : List α) (init : β) : β := s.foldr f init

def setCase (s : List α) (empty : β) (single : α → β) (otherwise : β) : β :=
  match s with
  | [] => empty
  | [x] => single x
  | _ :: _ => otherwise

def setChoose (s : List α) : α :=
  match s with
  | x :: _ => x
  | [] => sorry /- unreachable: choose is only defined for non-empty sets -/

def chooseAndSplit (cmp : α → α → LemOrdering) (s : List α) : Option (List α × α × List α) :=
  match s with
  | [] => none
  | x :: xs =>
    let lt := xs.filter (fun y => match cmp y x with | .LT => true | _ => false)
    let gt := xs.filter (fun y => match cmp y x with | .LT => false | .EQ => false | .GT => true)
    some (lt, x, gt)

/- Finite map operations (using List of pairs) -/
abbrev Fmap (α β : Type) := List (α × β)

def fmapEmpty : Fmap α β := []
@[inline] def fmapIsEmpty : Fmap α β → Bool := List.isEmpty

def fmapAdd [BEq α] (k : α) (v : β) (m : Fmap α β) : Fmap α β :=
  (k, v) :: m.filter (fun p => !(p.1 == k))

def fmapLookupBy (cmp : α → α → LemOrdering) (k : α) : Fmap α β → Option β
  | [] => none
  | (k', v) :: rest => match cmp k k' with
    | .EQ => some v
    | _ => fmapLookupBy cmp k rest

def fmapDeleteBy (cmp : α → α → LemOrdering) (k : α) (m : Fmap α β) : Fmap α β :=
  m.filter (fun p => match cmp k p.1 with | .EQ => false | _ => true)

def fmapMap (f : β → γ) (m : Fmap α β) : Fmap α γ :=
  m.map (fun p => (p.1, f p.2))

def fmapEqualBy (eqK : α → α → Bool) (eqV : β → β → Bool) (m1 m2 : Fmap α β) : Bool :=
  let check (m1 m2 : Fmap α β) : Bool :=
    m1.all (fun (k, v) =>
      match m2.find? (fun (k', _) => eqK k k') with
      | some (_, v') => eqV v v'
      | none => false)
  check m1 m2 && check m2 m1

def fmapDomainBy (cmp : α → α → LemOrdering) (m : Fmap α β) : List α :=
  setFromListBy cmp (m.map (fun p => p.1))

def fmapRangeBy (cmp : β → β → LemOrdering) (m : Fmap α β) : List β :=
  setFromListBy cmp (m.map (fun p => p.2))

def fmapAll (f : α → β → Bool) (m : Fmap α β) : Bool :=
  m.all (fun p => f p.1 p.2)

def fmapUnion [BEq α] (m1 m2 : Fmap α β) : Fmap α β :=
  m2.foldl (fun acc (k, v) => fmapAdd k v acc) m1

@[inline] def fmapElements (m : Fmap α β) : List (α × β) := m

/- Integer square root (floor of exact sqrt) -/
private partial def natSqrtAux (n guess : Nat) : Nat :=
  let next := (guess + n / guess) / 2
  if next >= guess then guess else natSqrtAux n next

def integerSqrt (n : Int) : Int :=
  let m := n.natAbs
  if m == 0 then 0 else Int.ofNat (natSqrtAux m m)

/- Rational/real stubs — Lem's rational/real types have no Lean equivalent.
   These panic rather than silently return wrong results. -/
def rationalNumerator (_n : Int) : Int :=
  panic! "rationalNumerator: rationals are not supported in the Lean backend"
def rationalDenominator (_n : Int) : Int :=
  panic! "rationalDenominator: rationals are not supported in the Lean backend"
def realSqrt (_n : Int) : Int :=
  panic! "realSqrt: reals are not supported in the Lean backend"
def realFloor (_n : Int) : Int :=
  panic! "realFloor: reals are not supported in the Lean backend"
def realCeiling (_n : Int) : Int :=
  panic! "realCeiling: reals are not supported in the Lean backend"

/- Integer absolute value returning Int (not Nat) -/
def intAbs (n : Int) : Int := Int.ofNat n.natAbs

/- List indexing wrappers -/
def listGet? (l : List α) (n : Nat) : Option α := l[n]?
def listGet! [Inhabited α] (l : List α) (n : Nat) : α := l[n]!

/- ============================================================ -/
/- Bitwise operations for fixed-width integers (represented as Int) -/
/- ============================================================ -/

/- Two's complement conversion helpers -/
private def toNat32 (x : Int) : Nat :=
  if x >= 0 then x.toNat % (2 ^ 32)
  else (2 ^ 32 - x.natAbs % (2 ^ 32)) % (2 ^ 32)

private def fromNat32 (n : Nat) : Int :=
  if n >= 2 ^ 31 then Int.ofNat n - Int.ofNat (2 ^ 32)
  else Int.ofNat n

private def toNat64 (x : Int) : Nat :=
  if x >= 0 then x.toNat % (2 ^ 64)
  else (2 ^ 64 - x.natAbs % (2 ^ 64)) % (2 ^ 64)

private def fromNat64 (n : Nat) : Int :=
  if n >= 2 ^ 63 then Int.ofNat n - Int.ofNat (2 ^ 64)
  else Int.ofNat n

/- int32 bitwise operations -/
def int32Lnot (x : Int) : Int := fromNat32 ((toNat32 x) ^^^ (2 ^ 32 - 1))
def int32Lor (x y : Int) : Int := fromNat32 ((toNat32 x) ||| (toNat32 y))
def int32Lxor (x y : Int) : Int := fromNat32 ((toNat32 x) ^^^ (toNat32 y))
def int32Land (x y : Int) : Int := fromNat32 ((toNat32 x) &&& (toNat32 y))
def int32Lsl (x : Int) (n : Nat) : Int := fromNat32 ((toNat32 x) <<< n)
def int32Lsr (x : Int) (n : Nat) : Int := fromNat32 ((toNat32 x) >>> n)
def int32Asr (x : Int) (n : Nat) : Int :=
  let sx := fromNat32 (toNat32 x)
  if sx < 0 then -((-sx - 1) >>> n) - 1
  else Int.ofNat (x.toNat >>> n)

/- int64 bitwise operations -/
def int64Lnot (x : Int) : Int := fromNat64 ((toNat64 x) ^^^ (2 ^ 64 - 1))
def int64Lor (x y : Int) : Int := fromNat64 ((toNat64 x) ||| (toNat64 y))
def int64Lxor (x y : Int) : Int := fromNat64 ((toNat64 x) ^^^ (toNat64 y))
def int64Land (x y : Int) : Int := fromNat64 ((toNat64 x) &&& (toNat64 y))
def int64Lsl (x : Int) (n : Nat) : Int := fromNat64 ((toNat64 x) <<< n)
def int64Lsr (x : Int) (n : Nat) : Int := fromNat64 ((toNat64 x) >>> n)
def int64Asr (x : Int) (n : Nat) : Int :=
  let sx := fromNat64 (toNat64 x)
  if sx < 0 then -((-sx - 1) >>> n) - 1
  else Int.ofNat (x.toNat >>> n)

/- ============================================================ -/
/- Missing library functions -/
/- ============================================================ -/

def naturalOfString (s : String) : Nat :=
  match s.toNat? with
  | some n => n
  | none => panic! s!"naturalOfString: invalid input: {s}"

def integerDiv_t (a b : Int) : Int := Int.tdiv a b
def integerRem_t (a b : Int) : Int := Int.tmod a b
def integerRem_f (a b : Int) : Int := Int.emod a b

def THE (_p : α → Bool) : Option α :=
  panic! "THE: Hilbert choice is not computable"

/- List indexing — replaces removed List.get? and List.get! -/
def listGetOpt (l : List α) (n : Nat) : Option α := l[n]?
def listGetBang [Inhabited α] (l : List α) (n : Nat) : α := l[n]!

/- List update (set element at index) — replaces removed List.set -/
def listSet (l : List α) (n : Nat) (v : α) : List α :=
  l.set n v

/- Convert a natural number to a list of bools (binary representation, LSB first) -/
partial def boolListFromNatural (acc : List Bool) (remainder : Nat) : List Bool :=
  if remainder > 0 then
    boolListFromNatural ((remainder % 2 == 1) :: acc) (remainder / 2)
  else
    acc.reverse

/- Bitwise binary operation on two bool lists, extending shorter with sign bit -/
partial def bitSeqBinopAux (binop : Bool → Bool → Bool) (s1 : Bool) (bl1 : List Bool)
    (s2 : Bool) (bl2 : List Bool) : List Bool :=
  match bl1, bl2 with
  | [], [] => []
  | b1 :: bl1', [] => (binop b1 s2) :: bitSeqBinopAux binop s1 bl1' s2 []
  | [], b2 :: bl2' => (binop s1 b2) :: bitSeqBinopAux binop s1 [] s2 bl2'
  | b1 :: bl1', b2 :: bl2' => (binop b1 b2) :: bitSeqBinopAux binop s1 bl1' s2 bl2'

/- Nat bitwise operations (used by transform.lem compatibility layer) -/
def natLand (a b : Nat) : Nat := a &&& b
def natLor (a b : Nat) : Nat := a ||| b
def natLxor (a b : Nat) : Nat := a ^^^ b
def natLnot (_a : Nat) : Nat := panic! "natLnot: bitwise NOT is not defined for Nat"
def natLsl (a b : Nat) : Nat := a <<< b
def natLsr (a b : Nat) : Nat := a >>> b
def natAsr (a b : Nat) : Nat := a >>> b  -- same as lsr for Nat (unsigned)

/- Transitive closure of a relation represented as a list of pairs.
   Iterates composition until no new pairs are added. Used by Relation module. -/
partial def set_tc (eq : α → α → Bool) (r : List (α × α)) : List (α × α) :=
  let mem (p : α × α) (s : List (α × α)) : Bool :=
    s.any (fun q => eq p.1 q.1 && eq p.2 q.2)
  let compose := r.foldl (fun acc (a, b) =>
    r.foldl (fun acc2 (c, d) =>
      let p := (a, d)
      if eq b c && !mem p acc2 then p :: acc2
      else acc2
    ) acc
  ) r
  if compose.length == r.length then r
  else set_tc eq compose
