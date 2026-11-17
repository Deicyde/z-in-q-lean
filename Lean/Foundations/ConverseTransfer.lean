import Std

namespace ConverseTransfer

/-- Parity of the values of a Boolean function on the cube of a given dimension. -/
def parity : Nat → (List Bool → Bool) → Bool
  | 0, f => f []
  | n + 1, f => xor (parity n (fun w => f (false :: w)))
                     (parity n (fun w => f (true :: w)))

/-- A true entry in the mask selects the corresponding variable in a squarefree monomial. -/
def monomial : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: mask, b :: w => (!a || b) && monomial mask w

def evaluate : List (List Bool) → List Bool → Bool
  | [], _ => false
  | mask :: ms, w => xor (monomial mask w) (evaluate ms w)

private theorem parity_zero (n : Nat) : parity n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [parity, ih]

private theorem interchange (a b c d : Bool) :
    xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem parity_add (n : Nat) (f g : List Bool → Bool) :
    parity n (fun w => xor (f w) (g w)) = xor (parity n f) (parity n g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [parity]
    rw [ih (fun w => f (false :: w)) (fun w => g (false :: w)),
        ih (fun w => f (true :: w)) (fun w => g (true :: w))]
    exact interchange _ _ _ _

private theorem monomial_even (mask : List Bool) (h : false ∈ mask) :
    parity mask.length (monomial mask) = false := by
  induction mask with
  | nil => simp at h
  | cons a mask ih =>
    cases a with
    | false => simp [parity, monomial]
    | true =>
      have hm : false ∈ mask := by simpa using h
      simp [parity, monomial, parity_zero, ih hm]

/-- Every polynomial all of whose monomials omit a variable has even total parity. -/
theorem cube_parity (n : Nat) (terms : List (List Bool))
    (ht : ∀ mask ∈ terms, mask.length = n ∧ false ∈ mask) :
    parity n (evaluate terms) = false := by
  induction terms with
  | nil => exact parity_zero n
  | cons a ps ih =>
    have ha := ht a (by simp)
    have hp := ih (fun m hm => ht m (by simp [hm]))
    change parity n (fun w => xor (monomial a w) (evaluate ps w)) = false
    rw [parity_add, hp, ← ha.1, monomial_even a ha.2]
    rfl

private theorem empty_parity (n : Nat) (f : List Bool → Bool)
    (hf : ∀ w, w.length = n → f w = false) : parity n f = false := by
  induction n generalizing f with
  | zero => exact hf [] rfl
  | succ n ih =>
    simp only [parity]
    rw [ih _ (fun w hw => hf (false :: w) (by simp [hw])),
        ih _ (fun w hw => hf (true :: w) (by simp [hw]))]
    rfl

private theorem origin_parity (n : Nat) (f : List Bool → Bool)
    (hf : ∀ w, w.length = n → w ≠ List.replicate n false → f w = false) :
    parity n f = f (List.replicate n false) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [parity]
    have hl := ih (fun w => f (false :: w)) (fun w hw hn =>
      hf (false :: w) (by simp [hw]) (by simpa [List.replicate_succ] using hn))
    have hr := empty_parity n (fun w => f (true :: w)) (fun w hw =>
      hf (true :: w) (by simp [hw]) (by simp [List.replicate_succ]))
    rw [hl, hr]
    simp [List.replicate_succ]

/-- When the origin is a solution, the parity test supplies a distinct solution. -/
theorem other_address (n : Nat) (terms : List (List Bool))
    (ht : ∀ mask ∈ terms, mask.length = n ∧ false ∈ mask)
    (h0 : evaluate terms (List.replicate n false) = true) :
    ∃ w : List Bool, w.length = n ∧ w ≠ List.replicate n false ∧ evaluate terms w = true := by
  classical
  by_cases h : ∃ w : List Bool, w.length = n ∧ w ≠ List.replicate n false ∧ evaluate terms w = true
  · exact h
  · have onlyOrigin : ∀ w, w.length = n → w ≠ List.replicate n false → evaluate terms w = false := by
      intro w hw hn
      cases he : evaluate terms w with
      | false => rfl
      | true => exact False.elim (h ⟨w, hw, hn, he⟩)
    have he := origin_parity n (evaluate terms) onlyOrigin
    rw [cube_parity n terms ht, h0] at he
    contradiction

/-- An evaluation table splits into its entries with leading bit zero and one. -/
inductive Table : Nat → Type where
  | leaf (b : Bool) : Table 0
  | node {n : Nat} (lo hi : Table n) : Table (n + 1)

def Table.add : Table n → Table n → Table n
  | .leaf a, .leaf b => .leaf (xor a b)
  | .node a b, .node c d => .node (a.add c) (b.add d)

def Table.weight : Table n → Nat
  | .leaf b => if b then 1 else 0
  | .node lo hi => lo.weight + hi.weight

/-- The recursive normal form f(x) + y g(x) of a binary polynomial of degree at most d. -/
inductive DegreeLE : {n : Nat} → Nat → Table n → Prop where
  | leaf (d : Nat) (b : Bool) : DegreeLE d (.leaf b)
  | independent {n d : Nat} {p : Table n} (h : DegreeLE d p) :
      DegreeLE d (.node p p)
  | affine {n d : Nat} {p q : Table n} (hp : DegreeLE (d+1) p) (hq : DegreeLE d q) :
      DegreeLE (d+1) (.node p (p.add q))

private theorem triangle_weight {n : Nat} (p q : Table n) :
    q.weight ≤ p.weight + (p.add q).weight := by
  induction p with
  | leaf x =>
    cases q with
    | leaf y => cases x <;> cases y <;> decide
  | node lo hi il ih =>
    cases q with
    | node a b =>
      have h₁ := il a
      have h₂ := ih b
      simp only [Table.weight, Table.add]
      omega

private theorem add_zero_weight {n : Nat} (p q : Table n) (h : q.weight = 0) :
    (p.add q).weight = p.weight := by
  induction p with
  | leaf x =>
    cases q with
    | leaf y => cases x <;> cases y <;> simp_all [Table.weight, Table.add]
  | node lo hi il ih =>
    cases q with
    | node a b =>
      simp only [Table.weight] at h
      have ha : a.weight = 0 := by omega
      have hb : b.weight = 0 := by omega
      simp only [Table.add, Table.weight, il a ha, ih b hb]

/-- A nonzero degree-d word has at least a 2^{-d} proportion of ones.
The scaled form also applies when d is greater than the cube dimension. -/
theorem minimum_weight {n d : Nat} {p : Table n}
    (h : DegreeLE d p) (positive : 0 < p.weight) : 2^n ≤ 2^d * p.weight := by
  induction h with
  | leaf d x =>
    cases x
    · contradiction
    · simp only [Table.weight, if_true, Nat.pow_zero, Nat.mul_one]
      exact Nat.pow_pos (by decide)
  | @independent n d p _ ih =>
    simp only [Table.weight] at positive ⊢
    have hp : 0 < p.weight := by omega
    rw [Nat.pow_succ, Nat.mul_add]
    have h' := ih hp
    omega
  | @affine n d p q _ _ ihp ihq =>
    simp only [Table.weight] at positive ⊢
    by_cases hq : q.weight = 0
    · have hw := add_zero_weight p q hq
      rw [hw] at positive ⊢
      have hp : 0 < p.weight := by omega
      rw [Nat.pow_succ 2 n, Nat.mul_add]
      have h' := ihp hp
      omega
    · have hn : 0 < q.weight := by omega
      have ht := Nat.mul_le_mul_left (2^d) (triangle_weight p q)
      have h' := Nat.mul_le_mul_right 2 (Nat.le_trans (ihq hn) ht)
      simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h'

end ConverseTransfer

#print axioms ConverseTransfer.cube_parity
#print axioms ConverseTransfer.other_address

#print axioms ConverseTransfer.minimum_weight
