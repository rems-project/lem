/- Lem standard library support for Lean 4 -/

/- DAEMON: undefined value placeholder, analogous to Coq's DAEMON axiom -/
axiom DAEMON : ∀ {α : Type}, α

/- Ordering type for comparisons -/
inductive LemOrdering where
  | LT : LemOrdering
  | EQ : LemOrdering
  | GT : LemOrdering
  deriving Repr, BEq, Inhabited

/- Bool/Prop bridge -/
def lemBoolToProp (b : Bool) : Prop := b = true

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

/- Integer operations -/
def intLtb (a b : Int) : Bool := a < b
def intLteb (a b : Int) : Bool := a ≤ b
def intGtb (a b : Int) : Bool := a > b
def intGteb (a b : Int) : Bool := a ≥ b

/- Set operations (using List as a simple set representation) -/
def setEmpty : List α := []
def setIsEmpty : List α → Bool := List.isEmpty
def setAdd [BEq α] (x : α) (s : List α) : List α :=
  if s.elem x then s else x :: s
def setMemberBy (eq : α → α → Bool) (x : α) (s : List α) : Bool :=
  listMemberBy eq x s
def setCardinal : List α → Nat := List.length
def setFromList [BEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if acc.elem x then acc else x :: acc) []
def setToList (s : List α) : List α := s

/- Finite map operations (using List of pairs) -/
abbrev Fmap (α β : Type) := List (α × β)

def fmapEmpty : Fmap α β := []
def fmapIsEmpty : Fmap α β → Bool := List.isEmpty
def fmapAdd [BEq α] (k : α) (v : β) (m : Fmap α β) : Fmap α β :=
  (k, v) :: m.filter (fun p => !(p.1 == k))
def fmapLookupBy (eq : α → α → Bool) (k : α) : Fmap α β → Option β
  | [] => none
  | (k', v) :: rest => if eq k k' then some v else fmapLookupBy eq k rest
def fmapDeleteBy (eq : α → α → Bool) (k : α) (m : Fmap α β) : Fmap α β :=
  m.filter (fun p => !(eq k p.1))
def fmapMap (f : β → γ) (m : Fmap α β) : Fmap α γ :=
  m.map (fun p => (p.1, f p.2))

/- Default values -/
instance : Inhabited LemOrdering := ⟨LemOrdering.EQ⟩
