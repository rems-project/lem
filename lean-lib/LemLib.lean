/- Lem standard library support for Lean 4 -/

/- DAEMON: undefined value placeholder, analogous to Coq's DAEMON axiom -/
axiom DAEMON : ∀ {α : Type}, α

/- Ordering type for comparisons -/
inductive LemOrdering where
  | LT : LemOrdering
  | EQ : LemOrdering
  | GT : LemOrdering
  deriving Repr, BEq, Inhabited

/- Ordering predicates -/
def isLess (o : LemOrdering) : Bool := o == .LT
def isLessEqual (o : LemOrdering) : Bool := o != .GT
def isGreater (o : LemOrdering) : Bool := o == .GT
def isGreaterEqual (o : LemOrdering) : Bool := o != .LT

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
def natPower (base exp : Nat) : Nat := base ^ exp
def natDiv (a b : Nat) : Nat := a / b
def natMod (a b : Nat) : Nat := a % b
def natMin (a b : Nat) : Nat := min a b
def natMax (a b : Nat) : Nat := max a b
def natLtb (a b : Nat) : Bool := a < b
def natLteb (a b : Nat) : Bool := a ≤ b
def natGtb (a b : Nat) : Bool := a > b
def natGteb (a b : Nat) : Bool := a ≥ b

/- Exponentiation by squaring -/
partial def gen_pow_aux (mul : α → α → α) (one : α) (base : α) (exp : Nat) : α :=
  match exp with
  | 0 => one
  | 1 => mul one base
  | _ =>
    let half := exp / 2
    let one' := if exp % 2 == 0 then one else mul one base
    gen_pow_aux mul one' (mul base base) half

/- Integer operations -/
def intLtb (a b : Int) : Bool := a < b
def intLteb (a b : Int) : Bool := a ≤ b
def intGtb (a b : Int) : Bool := a > b
def intGteb (a b : Int) : Bool := a ≥ b

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
def setIsEmpty : List α → Bool := List.isEmpty
def setSingleton (x : α) : List α := [x]

def setAdd [BEq α] (x : α) (s : List α) : List α :=
  if s.elem x then s else x :: s

def setMemberBy (cmp : α → α → LemOrdering) (x : α) (s : List α) : Bool :=
  match s with
  | [] => false
  | y :: ys => match cmp x y with
    | .EQ => true
    | _ => setMemberBy cmp x ys

def setCardinal : List α → Nat := List.length

def setFromList [BEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if acc.elem x then acc else x :: acc) []

def setFromListBy (cmp : α → α → LemOrdering) (l : List α) : List α :=
  l.foldl (fun acc x => if setMemberBy cmp x acc then acc else x :: acc) []

def setToList (s : List α) : List α := s

def setEqualBy (cmp : α → α → LemOrdering) (s1 s2 : List α) : Bool :=
  match s1 with
  | [] => s2.isEmpty
  | x :: xs => match s2 with
    | [] => false
    | y :: ys => match cmp x y with
      | .EQ => setEqualBy cmp xs ys
      | _ => false

def setCompareBy (cmp : α → α → LemOrdering) (s1 s2 : List α) : LemOrdering :=
  match s1, s2 with
  | [], [] => .EQ
  | [], _ :: _ => .LT
  | _ :: _, [] => .GT
  | x :: xs, y :: ys => match cmp x y with
    | .LT => .LT
    | .GT => .GT
    | .EQ => setCompareBy cmp xs ys

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

def setAny (f : α → Bool) (s : List α) : Bool := s.any f
def setForAll (f : α → Bool) (s : List α) : Bool := s.all f
def setFold (f : α → β → β) (s : List α) (init : β) : β := s.foldr f init

def setCase (s : List α) (empty : β) (single : α → β) (pair : α → List α → β) : β :=
  match s with
  | [] => empty
  | [x] => single x
  | x :: xs => pair x xs

def chooseAndSplit (_cmp : α → α → LemOrdering) (s : List α) : Option (List α × α × List α) :=
  match s with
  | [] => none
  | x :: xs =>
    let before : List α := []
    some (before, x, xs)

/- Finite map operations (using List of pairs) -/
abbrev Fmap (α β : Type) := List (α × β)

def fmapEmpty : Fmap α β := []
def fmapIsEmpty : Fmap α β → Bool := List.isEmpty

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

def fmapEqualBy (cmpK : α → α → LemOrdering) (cmpV : β → β → Bool) (m1 m2 : Fmap α β) : Bool :=
  let check (m1 m2 : Fmap α β) : Bool :=
    m1.all (fun (k, v) =>
      match fmapLookupBy cmpK k m2 with
      | some v' => cmpV v v'
      | none => false)
  check m1 m2 && check m2 m1

def fmapDomainBy (cmp : α → α → LemOrdering) (m : Fmap α β) : List α :=
  setFromListBy cmp (m.map (fun p => p.1))

def fmapRangeBy (cmp : β → β → LemOrdering) (m : Fmap α β) : List β :=
  setFromListBy cmp (m.map (fun p => p.2))

def fmapAll (f : α → β → Bool) (m : Fmap α β) : Bool :=
  m.all (fun p => f p.1 p.2)
