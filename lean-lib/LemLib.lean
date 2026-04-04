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

/- Vector slice: v.[i..j] extracts elements from index i to j (half-open) -/
namespace Vector
def slice [Inhabited α] {n m : Nat} (v : Vector α n) (start _stop : Nat) : Vector α m :=
  Vector.ofFn fun i => (v.toArray.extract start (start + m)).getD i.val default
end Vector

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

def setChoose [Inhabited α] (s : List α) : α :=
  match s with
  | x :: _ => x
  | [] => panic! "setChoose: empty set"

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

def fmapMapi (f : α → β → γ) (m : Fmap α β) : Fmap α γ :=
  m.map (fun p => (p.1, f p.1 p.2))

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

/- ============================================================================
   Unsupported numeric types
   ============================================================================
   Lem's rational, real, float64, and float32 types have no proper Lean
   implementation. Rather than silently mapping to Int (which produces
   semantically wrong results — e.g., rationalFromFrac 1 3 = 0 via integer
   division), we use distinct opaque types that panic on any operation.

   For proper support: rational needs Mathlib's Rat, real needs Mathlib's Real,
   and float64/float32 need IEEE 754 floats. Coq has similar limitations
   (float64/float32 map to Q, also approximate). -/

structure LemRational where
  private mk :: private val : Unit

structure LemReal where
  private mk :: private val : Unit

structure LemFloat64 where
  private mk :: private val : Unit

structure LemFloat32 where
  private mk :: private val : Unit

instance : Inhabited LemRational := ⟨⟨()⟩⟩
instance : BEq LemRational where beq _ _ := panic! "rational: not supported in Lean backend"
instance : Ord LemRational where compare _ _ := panic! "rational: not supported in Lean backend"
instance : Add LemRational where add _ _ := panic! "rational: not supported in Lean backend"
instance : Sub LemRational where sub _ _ := panic! "rational: not supported in Lean backend"
instance : Mul LemRational where mul _ _ := panic! "rational: not supported in Lean backend"
instance : Div LemRational where div _ _ := panic! "rational: not supported in Lean backend"
instance : Neg LemRational where neg _ := panic! "rational: not supported in Lean backend"
instance : HPow LemRational Int LemRational where hPow _ _ := panic! "rational: not supported in Lean backend"
instance : HPow LemRational Nat LemRational where hPow _ _ := panic! "rational: not supported in Lean backend"
instance : Min LemRational where min _ _ := panic! "rational: not supported in Lean backend"
instance : Max LemRational where max _ _ := panic! "rational: not supported in Lean backend"
instance (n : Nat) : OfNat LemRational n where ofNat := panic! "rational: not supported in Lean backend"

instance : Inhabited LemReal := ⟨⟨()⟩⟩
instance : BEq LemReal where beq _ _ := panic! "real: not supported in Lean backend"
instance : Ord LemReal where compare _ _ := panic! "real: not supported in Lean backend"
instance : Add LemReal where add _ _ := panic! "real: not supported in Lean backend"
instance : Sub LemReal where sub _ _ := panic! "real: not supported in Lean backend"
instance : Mul LemReal where mul _ _ := panic! "real: not supported in Lean backend"
instance : Div LemReal where div _ _ := panic! "real: not supported in Lean backend"
instance : Neg LemReal where neg _ := panic! "real: not supported in Lean backend"
instance : HPow LemReal Int LemReal where hPow _ _ := panic! "real: not supported in Lean backend"
instance : HPow LemReal Nat LemReal where hPow _ _ := panic! "real: not supported in Lean backend"
instance : Min LemReal where min _ _ := panic! "real: not supported in Lean backend"
instance : Max LemReal where max _ _ := panic! "real: not supported in Lean backend"
instance (n : Nat) : OfNat LemReal n where ofNat := panic! "real: not supported in Lean backend"

instance : Inhabited LemFloat64 := ⟨⟨()⟩⟩
instance : BEq LemFloat64 where beq _ _ := panic! "float64: not supported in Lean backend"
instance : Ord LemFloat64 where compare _ _ := panic! "float64: not supported in Lean backend"
instance (n : Nat) : OfNat LemFloat64 n where ofNat := panic! "float64: not supported in Lean backend"

instance : Inhabited LemFloat32 := ⟨⟨()⟩⟩
instance : BEq LemFloat32 where beq _ _ := panic! "float32: not supported in Lean backend"
instance : Ord LemFloat32 where compare _ _ := panic! "float32: not supported in Lean backend"
instance (n : Nat) : OfNat LemFloat32 n where ofNat := panic! "float32: not supported in Lean backend"

/- Target rep wrappers for rational operations that can't use infix operators -/
def unsupportedRationalFromNumeral (_ : Nat) : LemRational :=
  panic! "rational: not supported in Lean backend"
def unsupportedRationalFromInt (_ : Int) : LemRational :=
  panic! "rational: not supported in Lean backend"
def unsupportedRationalFromFrac (_ _ : Int) : LemRational :=
  panic! "rational: not supported in Lean backend"
def unsupportedRationalLess (_ _ : LemRational) : Bool :=
  panic! "rational: not supported in Lean backend"
def unsupportedRationalLessEq (_ _ : LemRational) : Bool :=
  panic! "rational: not supported in Lean backend"
def unsupportedRationalGreater (_ _ : LemRational) : Bool :=
  panic! "rational: not supported in Lean backend"
def unsupportedRationalGreaterEq (_ _ : LemRational) : Bool :=
  panic! "rational: not supported in Lean backend"

/- Target rep wrappers for real operations that can't use infix operators -/
def unsupportedRealFromNumeral (_ : Nat) : LemReal :=
  panic! "real: not supported in Lean backend"
def unsupportedRealFromInt (_ : Int) : LemReal :=
  panic! "real: not supported in Lean backend"
def unsupportedRealFromFrac (_ _ : Int) : LemReal :=
  panic! "real: not supported in Lean backend"
def unsupportedRealLess (_ _ : LemReal) : Bool :=
  panic! "real: not supported in Lean backend"
def unsupportedRealLessEq (_ _ : LemReal) : Bool :=
  panic! "real: not supported in Lean backend"
def unsupportedRealGreater (_ _ : LemReal) : Bool :=
  panic! "real: not supported in Lean backend"
def unsupportedRealGreaterEq (_ _ : LemReal) : Bool :=
  panic! "real: not supported in Lean backend"
def unsupportedRealAbs (_ : LemReal) : LemReal :=
  panic! "real: not supported in Lean backend"

/- Integer square root (floor of exact sqrt) -/
private partial def natSqrtAux (n guess : Nat) : Nat :=
  let next := (guess + n / guess) / 2
  if next >= guess then guess else natSqrtAux n next

def integerSqrt (n : Int) : Int :=
  let m := n.natAbs
  if m == 0 then 0 else Int.ofNat (natSqrtAux m m)

/- Target rep wrappers for rational/real decomposition operations -/
def rationalNumerator (_ : LemRational) : Int :=
  panic! "rational: not supported in Lean backend"
def rationalDenominator (_ : LemRational) : Int :=
  panic! "rational: not supported in Lean backend"
def realSqrt (_ : LemReal) : LemReal :=
  panic! "real: not supported in Lean backend"
def realFloor (_ : LemReal) : Int :=
  panic! "real: not supported in Lean backend"
def realCeiling (_ : LemReal) : Int :=
  panic! "real: not supported in Lean backend"

/- Integer absolute value returning Int (not Nat) -/
def intAbs (n : Int) : Int := Int.ofNat n.natAbs

/- List indexing wrappers -/
def listGet? (l : List α) (n : Nat) : Option α := l[n]?
def listGet! [Inhabited α] (l : List α) (n : Nat) : α := l[n]!

/- ============================================================ -/
/- Fixed-width integer types                                   -/
/- ============================================================ -/
/- Lem's int32 and int64 types are represented as distinct newtype wrappers
   around Int. This provides type safety (can't accidentally mix int32/int64/int)
   and eliminates duplicate typeclass instances. Arithmetic uses Int operations
   (arbitrary precision, no overflow) — same semantics as Coq's Z mapping.
   For proper overflow semantics, these would need BitVec 32/BitVec 64. -/

structure LemInt32 where val : Int
structure LemInt64 where val : Int

instance : Inhabited LemInt32 := ⟨⟨0⟩⟩
instance : BEq LemInt32 where beq a b := a.val == b.val
instance : Ord LemInt32 where compare a b := compare a.val b.val
instance : Add LemInt32 where add a b := ⟨a.val + b.val⟩
instance : Sub LemInt32 where sub a b := ⟨a.val - b.val⟩
instance : Mul LemInt32 where mul a b := ⟨a.val * b.val⟩
instance : Div LemInt32 where div a b := ⟨a.val / b.val⟩
instance : Mod LemInt32 where mod a b := ⟨a.val % b.val⟩
instance : Neg LemInt32 where neg a := ⟨-a.val⟩
instance : HPow LemInt32 Nat LemInt32 where hPow a n := ⟨a.val ^ n⟩
instance : Min LemInt32 where min a b := if a.val <= b.val then a else b
instance : Max LemInt32 where max a b := if a.val >= b.val then a else b
instance (n : Nat) : OfNat LemInt32 n where ofNat := ⟨n⟩

instance : Inhabited LemInt64 := ⟨⟨0⟩⟩
instance : BEq LemInt64 where beq a b := a.val == b.val
instance : Ord LemInt64 where compare a b := compare a.val b.val
instance : Add LemInt64 where add a b := ⟨a.val + b.val⟩
instance : Sub LemInt64 where sub a b := ⟨a.val - b.val⟩
instance : Mul LemInt64 where mul a b := ⟨a.val * b.val⟩
instance : Div LemInt64 where div a b := ⟨a.val / b.val⟩
instance : Mod LemInt64 where mod a b := ⟨a.val % b.val⟩
instance : Neg LemInt64 where neg a := ⟨-a.val⟩
instance : HPow LemInt64 Nat LemInt64 where hPow a n := ⟨a.val ^ n⟩
instance : Min LemInt64 where min a b := if a.val <= b.val then a else b
instance : Max LemInt64 where max a b := if a.val >= b.val then a else b
instance (n : Nat) : OfNat LemInt64 n where ofNat := ⟨n⟩

/- Target rep wrappers for int32 operations -/
def lemInt32Ltb (a b : LemInt32) : Bool := a.val < b.val
def lemInt32Lteb (a b : LemInt32) : Bool := a.val <= b.val
def lemInt32Gtb (a b : LemInt32) : Bool := a.val > b.val
def lemInt32Gteb (a b : LemInt32) : Bool := a.val >= b.val
def lemInt32Abs (a : LemInt32) : LemInt32 := ⟨Int.ofNat a.val.natAbs⟩
def lemInt32OfNat (n : Nat) : LemInt32 := ⟨Int.ofNat n⟩
def lemInt32OfInt (n : Int) : LemInt32 := ⟨n⟩
def lemInt32ToInt (n : LemInt32) : Int := n.val
def lemInt32ToNat (n : LemInt32) : Nat := Int.toNat n.val
def lemInt32FromInt64 (n : LemInt64) : LemInt32 := ⟨n.val⟩

/- Target rep wrappers for int64 operations -/
def lemInt64Ltb (a b : LemInt64) : Bool := a.val < b.val
def lemInt64Lteb (a b : LemInt64) : Bool := a.val <= b.val
def lemInt64Gtb (a b : LemInt64) : Bool := a.val > b.val
def lemInt64Gteb (a b : LemInt64) : Bool := a.val >= b.val
def lemInt64Abs (a : LemInt64) : LemInt64 := ⟨Int.ofNat a.val.natAbs⟩
def lemInt64OfNat (n : Nat) : LemInt64 := ⟨Int.ofNat n⟩
def lemInt64OfInt (n : Int) : LemInt64 := ⟨n⟩
def lemInt64ToInt (n : LemInt64) : Int := n.val
def lemInt64FromInt32 (n : LemInt32) : LemInt64 := ⟨n.val⟩

/- ============================================================ -/
/- Bitwise operations for fixed-width integers                  -/
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
def int32Lnot (x : LemInt32) : LemInt32 := ⟨fromNat32 ((toNat32 x.val) ^^^ (2 ^ 32 - 1))⟩
def int32Lor (x y : LemInt32) : LemInt32 := ⟨fromNat32 ((toNat32 x.val) ||| (toNat32 y.val))⟩
def int32Lxor (x y : LemInt32) : LemInt32 := ⟨fromNat32 ((toNat32 x.val) ^^^ (toNat32 y.val))⟩
def int32Land (x y : LemInt32) : LemInt32 := ⟨fromNat32 ((toNat32 x.val) &&& (toNat32 y.val))⟩
def int32Lsl (x : LemInt32) (n : Nat) : LemInt32 := ⟨fromNat32 ((toNat32 x.val) <<< n)⟩
def int32Lsr (x : LemInt32) (n : Nat) : LemInt32 := ⟨fromNat32 ((toNat32 x.val) >>> n)⟩
def int32Asr (x : LemInt32) (n : Nat) : LemInt32 :=
  let sx := fromNat32 (toNat32 x.val)
  ⟨if sx < 0 then -((-sx - 1) >>> n) - 1
  else Int.ofNat (x.val.toNat >>> n)⟩

/- int64 bitwise operations -/
def int64Lnot (x : LemInt64) : LemInt64 := ⟨fromNat64 ((toNat64 x.val) ^^^ (2 ^ 64 - 1))⟩
def int64Lor (x y : LemInt64) : LemInt64 := ⟨fromNat64 ((toNat64 x.val) ||| (toNat64 y.val))⟩
def int64Lxor (x y : LemInt64) : LemInt64 := ⟨fromNat64 ((toNat64 x.val) ^^^ (toNat64 y.val))⟩
def int64Land (x y : LemInt64) : LemInt64 := ⟨fromNat64 ((toNat64 x.val) &&& (toNat64 y.val))⟩
def int64Lsl (x : LemInt64) (n : Nat) : LemInt64 := ⟨fromNat64 ((toNat64 x.val) <<< n)⟩
def int64Lsr (x : LemInt64) (n : Nat) : LemInt64 := ⟨fromNat64 ((toNat64 x.val) >>> n)⟩
def int64Asr (x : LemInt64) (n : Nat) : LemInt64 :=
  let sx := fromNat64 (toNat64 x.val)
  ⟨if sx < 0 then -((-sx - 1) >>> n) - 1
  else Int.ofNat (x.val.toNat >>> n)⟩

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
def boolListFromNatural (acc : List Bool) (remainder : Nat) : List Bool :=
  if h : remainder > 0 then
    boolListFromNatural ((remainder % 2 == 1) :: acc) (remainder / 2)
  else
    acc.reverse
termination_by remainder
decreasing_by exact Nat.div_lt_self h (by omega)

/- Bitwise binary operation on two bool lists, extending shorter with sign bit -/
def bitSeqBinopAux (binop : Bool → Bool → Bool) (s1 : Bool) (bl1 : List Bool)
    (s2 : Bool) (bl2 : List Bool) : List Bool :=
  match bl1, bl2 with
  | [], [] => []
  | b1 :: bl1', [] => (binop b1 s2) :: bitSeqBinopAux binop s1 bl1' s2 []
  | [], b2 :: bl2' => (binop s1 b2) :: bitSeqBinopAux binop s1 [] s2 bl2'
  | b1 :: bl1', b2 :: bl2' => (binop b1 b2) :: bitSeqBinopAux binop s1 bl1' s2 bl2'
termination_by bl1.length + bl2.length

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

/- ============================================================ -/
/- Total implementations for generated library functions         -/
/- ============================================================ -/

/- Total stringFromNatHelper: converts nat to digit chars via n/10 recursion -/
def lemStringFromNatHelper (n : Nat) (acc : List Char) : List Char :=
  if h : n = 0 then acc
  else lemStringFromNatHelper (n / 10) (Char.ofNat ((n % 10) + 48) :: acc)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/- Total stringFromNaturalHelper: identical logic (natural = nat in Lean) -/
def lemStringFromNaturalHelper (n : Nat) (acc : List Char) : List Char :=
  if h : n = 0 then acc
  else lemStringFromNaturalHelper (n / 10) (Char.ofNat ((n % 10) + 48) :: acc)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/- ========================================================================
   Machine word (mword / BitVec) operations
   ======================================================================== -/

/- Conversion operations -/
def mwordFromInteger {n : Nat} (i : Int) : BitVec n := BitVec.ofInt n i
def mwordFromNatural {n : Nat} (i : Nat) : BitVec n := BitVec.ofNat n i
def mwordSignedToInteger {n : Nat} (w : BitVec n) : Int := w.toInt
def mwordUnsignedToInteger {n : Nat} (w : BitVec n) : Int := Int.ofNat w.toNat
def mwordNaturalFromWord {n : Nat} (w : BitVec n) : Nat := w.toNat

/- Bitwise operations -/
def mwordLAnd {n : Nat} (a b : BitVec n) : BitVec n := a &&& b
def mwordLOr {n : Nat} (a b : BitVec n) : BitVec n := a ||| b
def mwordLXor {n : Nat} (a b : BitVec n) : BitVec n := a ^^^ b
def mwordLNot {n : Nat} (a : BitVec n) : BitVec n := ~~~a

/- Shift operations (Lem uses Nat for shift amount) -/
def mwordShiftLeft {n : Nat} (w : BitVec n) (s : Nat) : BitVec n := w <<< s
def mwordShiftRight {n : Nat} (w : BitVec n) (s : Nat) : BitVec n := w >>> s
def mwordArithShiftRight {n : Nat} (w : BitVec n) (s : Nat) : BitVec n := BitVec.sshiftRight w s

/- Rotate operations -/
def mwordRotateLeft {n : Nat} (s : Nat) (w : BitVec n) : BitVec n := BitVec.rotateLeft w s
def mwordRotateRight {n : Nat} (s : Nat) (w : BitVec n) : BitVec n := BitVec.rotateRight w s

/- Bit access -/
def mwordGetBit {n : Nat} (w : BitVec n) (i : Nat) : Bool := w.getLsbD i
def mwordSetBit {n : Nat} (w : BitVec n) (i : Nat) (b : Bool) : BitVec n :=
  if b then w ||| (BitVec.ofNat n (1 <<< i))
  else w &&& ~~~(BitVec.ofNat n (1 <<< i))
def mwordMsb {n : Nat} (w : BitVec n) : Bool := w.msb
def mwordLsb {n : Nat} (w : BitVec n) : Bool := w.getLsbD 0

/- Arithmetic operations -/
def mwordPlus {n : Nat} (a b : BitVec n) : BitVec n := a + b
def mwordMinus {n : Nat} (a b : BitVec n) : BitVec n := a - b
def mwordUminus {n : Nat} (a : BitVec n) : BitVec n := -a
def mwordTimes {n : Nat} (a b : BitVec n) : BitVec n := a * b
def mwordUnsignedDivide {n : Nat} (a b : BitVec n) : BitVec n := BitVec.udiv a b
def mwordSignedDivide {n : Nat} (a b : BitVec n) : BitVec n := BitVec.sdiv a b
def mwordModulo {n : Nat} (a b : BitVec n) : BitVec n := BitVec.umod a b

/- Comparison operations -/
def mwordEq {n : Nat} (a b : BitVec n) : Bool := a == b
def mwordSignedLess {n : Nat} (a b : BitVec n) : Bool := BitVec.slt a b
def mwordSignedLessEq {n : Nat} (a b : BitVec n) : Bool := BitVec.sle a b
def mwordUnsignedLess {n : Nat} (a b : BitVec n) : Bool := BitVec.ult a b
def mwordUnsignedLessEq {n : Nat} (a b : BitVec n) : Bool := BitVec.ule a b

/- Word concatenation and extraction -/
def mwordConcat {n m result : Nat} (a : BitVec n) (b : BitVec m) : BitVec result :=
  (a ++ b).setWidth result
def mwordExtract {n result : Nat} (lo _hi : Nat) (w : BitVec n) : BitVec result :=
  -- Lem passes (lo, hi, word); result width comes from the return type.
  -- hi is redundant (same as Isabelle's Word.slice which also ignores hi).
  BitVec.extractLsb' lo result w
def mwordUpdate {n m : Nat} (w : BitVec n) (lo _hi : Nat) (v : BitVec m) : BitVec n :=
  -- Lem passes (word, lo, hi, value); hi is redundant given v's width m.
  let mask := ~~~(BitVec.ofNat n (((1 <<< m) - 1) <<< lo))
  let shifted := BitVec.ofNat n (v.toNat <<< lo)
  (w &&& mask) ||| shifted

/- Width operations -/
def mwordZeroExtend {w v : Nat} (a : BitVec w) : BitVec v := BitVec.zeroExtend v a
def mwordSignExtend {w v : Nat} (a : BitVec w) : BitVec v := BitVec.signExtend v a

/- Word length -/
def mwordLength {n : Nat} (_ : BitVec n) : Nat := n

/- Hex display -/
def mwordToHex {n : Nat} (w : BitVec n) : String := BitVec.toHex w

/- Bitlist conversion -/
def mwordFromBitlist {n : Nat} (bits : List Bool) : BitVec n :=
  -- Convert LSB-first list of bools to BitVec
  let val := bits.foldl (fun (acc : Nat × Nat) b =>
    (acc.1 + (if b then 1 <<< acc.2 else 0), acc.2 + 1)) (0, 0)
  BitVec.ofNat n val.1

def mwordToBitlist {n : Nat} (w : BitVec n) : List Bool :=
  List.map (fun i => w.getLsbD i) (List.range n)

/- Total leastFixedPoint: bounded set iteration with explicit comparator -/
def lemLeastFixedPoint (cmp : α → α → LemOrdering) (bound : Nat)
    (f : List α → List α) (x : List α) : List α :=
  if h : bound = 0 then x
  else
    let fx := f x
    if setSubsetBy cmp fx x then x
    else lemLeastFixedPoint cmp (bound - 1) f (setUnionBy cmp fx x)
termination_by bound
decreasing_by omega
