import Std

namespace ZeroInput.Sparse

/-- The input is slot 1. A repeated coordinate in a monomial contributes a power. -/
structure Term where
  coefficient : Int
  monomial : List Nat
  deriving Repr

def monomialValue (x : Nat → Rat) : List Nat → Rat
  | [] => 1
  | i :: rest => x i * monomialValue x rest

def termValue (x : Nat → Rat) (t : Term) : Rat :=
  (t.coefficient : Rat) * monomialValue x t.monomial

def value (x : Nat → Rat) : List Term → Rat
  | [] => 0
  | t :: rest => termValue x t + value x rest

theorem value_append (x : Nat → Rat) (a b : List Term) :
    value x (a ++ b) = value x a + value x b := by
  induction a with
  | nil => simp [value, Rat.zero_add]
  | cons t ts ih => simp [value, ih, Rat.add_assoc]

/-- A term in source order, with one distinguished factor. -/
structure Factor where
  coefficient : Int
  before : List Nat
  code : Nat
  after : List Nat

def Factor.term (slot : Nat → Nat) (t : Factor) : Term :=
  ⟨t.coefficient, t.before ++ (slot t.code :: t.after)⟩

theorem vanishing_factor (x : Nat → Rat) (j : Nat) (hj : x j = 0)
    (before after : List Nat) : monomialValue x (before ++ (j :: after)) = 0 := by
  induction before with
  | nil => simp [monomialValue, hj]
  | cons i is ih => simp [monomialValue, ih]

theorem vanishing_block (x : Nat → Rat) (slot : Nat → Nat)
    (hx : ∀ c, x (slot c) = 0) (terms : List Factor) :
    value x (terms.map (Factor.term slot)) = 0 := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, value, termValue, Factor.term, ih]
    rw [vanishing_factor x _ (hx _)]; simp [Rat.zero_add]

/-- Compact text is used only for the closed polynomial data. -/
def decodeIndices (s : String) : Option (List Nat) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM String.toNat?

def decodeFactor (s : String) : Option Factor := do
  let [c, left, i, right] := s.splitOn "|" | none
  return ⟨← c.toInt?, ← decodeIndices left, ← i.toNat?, ← decodeIndices right⟩

def chunk (slot : Nat → Nat) (payload : String) : List Term :=
  ((payload.splitOn ";").filterMap decodeFactor).map (Factor.term slot)

def blocks (slot : Nat → Nat) (payloads : List String) : List Term :=
  payloads.flatMap (chunk slot)

theorem blocks_zero (x : Nat → Rat) (slot : Nat → Nat)
    (hx : ∀ c, x (slot c) = 0) (payloads : List String) :
    value x (blocks slot payloads) = 0 := by
  induction payloads with
  | nil => rfl
  | cons s ss ih =>
    change value x (chunk slot s ++ blocks slot ss) = 0
    rw [value_append, ih, Rat.add_zero]
    exact vanishing_block x slot hx _

def origin (_ : Nat) : Rat := 0

/-- Interpret a zero-based finite vector at the one-based coordinates of the table. -/
def finiteLift {n : Nat} (x : Fin n → Rat) : Nat → Rat
  | 0 => 0
  | i + 1 => if hi : i < n then x ⟨i, hi⟩ else 0

theorem finite_origin (n : Nat) : finiteLift (fun _ : Fin n => (0 : Rat)) = origin := by
  funext j
  cases j with
  | zero => rfl
  | succ i => simp [finiteLift, origin]

def outside (n : Nat) : Nat := if n < 199 then n else n + 2

def plane (u v : Rat) (n : Nat) : Rat :=
  if n = 199 then u else if n = 200 then v else 0

theorem plane_outside (u v : Rat) (n : Nat) : plane u v (outside n) = 0 := by
  have h₁ : outside n ≠ 199 := by unfold outside; split <;> omega
  have h₂ : outside n ≠ 200 := by unfold outside; split <;> omega
  simp [plane, h₁, h₂]

theorem origin_blocks (strings : List String) : value origin (blocks id strings) = 0 :=
  blocks_zero origin id (fun _ => rfl) strings

theorem plane_blocks (u v : Rat) (strings : List String) :
    value (plane u v) (blocks outside strings) = 0 :=
  blocks_zero (plane u v) outside (plane_outside u v) strings

def r0 : Rat := 444713220000

end ZeroInput.Sparse
