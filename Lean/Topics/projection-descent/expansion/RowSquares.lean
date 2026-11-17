import SparseWitness

namespace RowSquares

open ZeroInput.Sparse

private theorem monomial_perm (x : Nat → Rat) {a b : List Nat} (h : a.Perm b) :
    monomialValue x a = monomialValue x b := by
  induction h with
  | nil => rfl
  | cons i h ih => simp only [monomialValue, ih]
  | swap i j l => simp only [monomialValue]; grobner
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem value_perm (x : Nat → Rat) {a b : List Term} (h : a.Perm b) :
    value x a = value x b := by
  induction h with
  | nil => rfl
  | cons i h ih => simp only [value, ih]
  | swap i j l => simp only [value]; grobner
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem monomial_append (x : Nat → Rat) (a b : List Nat) :
    monomialValue x (a ++ b) = monomialValue x a * monomialValue x b := by
  induction a with
  | nil => simp [monomialValue]
  | cons i is ih => simp only [List.cons_append, monomialValue, ih]; grobner

def productTerm (a b : Term) : Term :=
  ⟨a.coefficient * b.coefficient, (a.monomial ++ b.monomial).mergeSort⟩

theorem term_product (x : Nat → Rat) (a b : Term) :
    termValue x (productTerm a b) = termValue x a * termValue x b := by
  unfold termValue productTerm
  simp only [Rat.intCast_mul]
  rw [monomial_perm x (List.mergeSort_perm _ _), monomial_append]
  grobner

-- A finished run of zero coefficient is omitted from the canonical list.
private def store (t : Term) (rev : List Term) : List Term :=
  if t.coefficient = 0 then rev else t :: rev

private theorem store_value (x : Nat → Rat) (t : Term) (rev : List Term) :
    value x (store t rev) = termValue x t + value x rev := by
  unfold store
  split
  · rename_i h; simp [termValue, h, Rat.zero_add]
  · rfl

private def collectRuns : List Term → Term → List Term → List Term
  | [], pending, rev => (store pending rev).reverse
  | t :: rest, pending, rev =>
      if t.monomial = pending.monomial then
        collectRuns rest ⟨pending.coefficient + t.coefficient, pending.monomial⟩ rev
      else collectRuns rest t (store pending rev)

private theorem runs_value (x : Nat → Rat) (rest : List Term) (t : Term) (rev : List Term) :
    value x (collectRuns rest t rev) = value x rev + termValue x t + value x rest := by
  induction rest generalizing t rev with
  | nil =>
    unfold collectRuns
    rw [value_perm x (List.reverse_perm _), store_value]
    simp only [value]; grobner
  | cons h rest ih =>
    unfold collectRuns
    split
    · rename_i same
      rw [ih]; simp only [value, termValue, Rat.intCast_add, same]; grobner
    · rw [ih, store_value]; simp only [value]; grobner

private def termOrder (a b : Term) : Bool :=
  if a.monomial.length = b.monomial.length then compare a.monomial b.monomial != .gt
  else decide (a.monomial.length ≤ b.monomial.length)

def collect (l : List Term) : List Term :=
  match l.mergeSort termOrder with
  | [] => []
  | t :: rest => collectRuns rest t []

theorem collect_value (x : Nat → Rat) (l : List Term) : value x (collect l) = value x l := by
  unfold collect
  split
  · rename_i h
    have perm := List.mergeSort_perm l termOrder
    rw [h] at perm
    exact value_perm x perm
  · rename_i t rest h
    have perm := List.mergeSort_perm l termOrder
    rw [h] at perm
    rw [runs_value, ← value_perm x perm]
    simp [value, Rat.zero_add]

def product (a b : List Term) : List Term :=
  a.flatMap fun t => b.map (productTerm t)

private theorem times_row (x : Nat → Rat) (t : Term) (row : List Term) :
    value x (row.map (productTerm t)) = termValue x t * value x row := by
  induction row with
  | nil => simp [value]
  | cons head tail ih => simp only [List.map_cons, value, term_product, ih]; grobner

theorem product_value (x : Nat → Rat) (a b : List Term) :
    value x (product a b) = value x a * value x b := by
  induction a with
  | nil => simp [product, value]
  | cons head tail ih =>
    change value x (b.map (productTerm head) ++ product tail b) = _
    rw [value_append, times_row, ih]
    simp only [value]; grobner

abbrev Rows := List (Nat × List Term)

def expansion (rows : Rows) : List Term :=
  collect (rows.flatMap fun row => collect (product row.2 row.2))

def sumSquares (x : Nat → Rat) : Rows → Rat
  | [] => 0
  | r :: rows => value x r.2 * value x r.2 + sumSquares x rows

theorem expansion_value (x : Nat → Rat) (rows : Rows) :
    value x (expansion rows) = sumSquares x rows := by
  unfold expansion
  rw [collect_value]
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rw [List.flatMap_cons, value_append, collect_value, product_value, ih]
    rfl

private theorem square_nonneg (a : Rat) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Rat.mul_nonneg h h
  · have hn : 0 ≤ -a := by grind
    have hh := Rat.mul_nonneg hn hn
    have eq : (-a) * (-a) = a*a := by grobner
    rwa [eq] at hh

private theorem sum_nonneg (x : Nat → Rat) (rows : Rows) : 0 ≤ sumSquares x rows := by
  induction rows with
  | nil => exact Rat.le_refl
  | cons row rest ih => exact Rat.add_nonneg (square_nonneg _) ih

theorem zero_iff_rows (x : Nat → Rat) (rows : Rows) :
    value x (expansion rows) = 0 ↔ ∀ r ∈ rows, value x r.2 = 0 := by
  rw [expansion_value]
  induction rows with
  | nil => simp [sumSquares]
  | cons row rest ih =>
    have h := sum_nonneg x rest
    have sq := square_nonneg (value x row.2)
    simp only [sumSquares, List.forall_mem_cons]
    constructor
    · intro hz
      have rz : sumSquares x rest = 0 := by grind
      have prodz : value x row.2 * value x row.2 = 0 := by grind
      have vz := (Rat.mul_eq_zero.mp prodz).elim id id
      exact ⟨vz, ih.mp rz⟩
    · rintro ⟨rz, restz⟩
      simp [rz, ih.mpr restz, Rat.zero_add]

#print axioms term_product
#print axioms collect_value
#print axioms product_value
#print axioms expansion_value
#print axioms zero_iff_rows

end RowSquares
