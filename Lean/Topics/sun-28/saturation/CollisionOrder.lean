import BoundedSeparator
import Mathlib.Algebra.Polynomial.RingDivision

/-! The order at zero of the polynomial of ordered pairwise differences. -/
open Polynomial Finset
namespace Sun28.Collision
open ZInQBlueprint.SunTower
noncomputable section
variable {K ι : Type*} [Field K]

/-- The difference parameter is the polynomial indeterminate. The two indices form an ordered pair. -/
def differences (S : Finset ι) (ell : ι → K) (wt : ι → ℕ) : K[X] :=
  ∏ z ∈ S ×ˢ S, (X-C (ell z.2-ell z.1))^(wt z.1*wt z.2)

theorem order_differences [DecidableEq K] (S : Finset ι) (ell : ι → K) (wt : ι → ℕ) :
    (differences S ell wt).rootMultiplicity 0 =
      ∑ z ∈ S ×ˢ S, if ell z.1=ell z.2 then wt z.1*wt z.2 else 0 := by
  classical
  let g (z : ι×ι) : K[X] := (X-C (ell z.2-ell z.1))^(wt z.1*wt z.2)
  have nz (z : ι×ι) : g z ≠ 0 := ((monic_X_sub_C _).pow _).ne_zero
  have term (z : ι×ι) : (g z).rootMultiplicity 0 =
      if ell z.1=ell z.2 then wt z.1*wt z.2 else 0 := by
    by_cases h : ell z.1=ell z.2
    · simp only [h,ite_true,g,sub_self]; exact rootMultiplicity_X_sub_C_pow 0 _
    · simp only [ite_eq_right h]
      by_cases he : wt z.1*wt z.2=0
      · simp [g,he]
      · apply rootMultiplicity_eq_zero
        simp [IsRoot,g,eval_pow,h,sub_ne_zero,he]
  have all (T : Finset (ι×ι)) : (∏ z ∈ T,g z).rootMultiplicity 0 =
      ∑ z ∈ T, if ell z.1=ell z.2 then wt z.1*wt z.2 else 0 := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert x T hx ih =>
      rw [Finset.prod_insert hx,Finset.sum_insert hx,
        rootMultiplicity_mul (mul_ne_zero (nz _) (Finset.prod_ne_zero_iff.mpr (fun z _ => nz z))),
        term,ih]
  exact all _

theorem order_eq_diagonal_iff (S : Finset ι) (ell : ι → K) (wt : ι → ℕ)
    (positive : ∀ x ∈ S, 0<wt x) :
    (differences S ell wt).rootMultiplicity 0 = ∑ x ∈ S, wt x^2 ↔
      Set.InjOn ell (S : Set ι) := by
  classical
  let diag (z : ι×ι) := if z.1=z.2 then wt z.1*wt z.2 else 0
  let hit (z : ι×ι) := if ell z.1=ell z.2 then wt z.1*wt z.2 else 0
  have dsum : ∑ z ∈ S ×ˢ S, diag z = ∑ x ∈ S, wt x^2 := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x hx
    simp [diag,hx,pow_two]
  have le (z : ι×ι) : diag z ≤ hit z := by
    by_cases e : z.1=z.2 <;> simp [diag,hit,e]
  rw [order_differences,←dsum]
  change (∑ z ∈ S ×ˢ S, hit z) = _ ↔ _
  constructor
  · intro eq x hx y hy same
    by_contra neq
    have mem : (x,y) ∈ S ×ˢ S := Finset.mem_product.mpr ⟨hx,hy⟩
    have strict : diag (x,y) < hit (x,y) := by
      simp [diag,hit,neq,same,Nat.mul_pos (positive x hx) (positive y hy)]
    exact (ne_of_lt (Finset.sum_lt_sum (fun z _ => le z) ⟨(x,y),mem,strict⟩)) eq.symm
  · intro hi
    apply Finset.sum_congr rfl
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    by_cases e : ell x=ell y
    · have same : x=y := hi hx hy e
      subst y
      simp [hit,diag]
    · have n : x≠y := fun h => e (h ▸ rfl)
      simp [hit,diag,e,n]

theorem diagonal_le_order (S : Finset ι) (ell : ι → K) (wt : ι → ℕ) :
    (∑ x ∈ S, wt x^2) ≤ (differences S ell wt).rootMultiplicity 0 := by
  classical
  rw [order_differences,Finset.sum_product]
  apply Finset.sum_le_sum
  intro x hx
  simpa [pow_two] using
    (Finset.single_le_sum (f:=fun y => if ell x=ell y then wt x*wt y else 0)
      (fun i _ => Nat.zero_le _) hx)

theorem separates_iff_minimizes [CharZero K] {n : ℕ} (S : Finset (Fin n → K))
    (wt : (Fin n → K) → ℕ) (positive : ∀ x ∈ S, 0<wt x)
    (b B : ℕ) (bound : S.card.choose 2*(n-1) ≤ B) :
    Set.InjOn (separator (b:K)) (S : Set (Fin n → K)) ↔
      ∀ j : ℕ, j≤B → (differences S (separator (b:K)) wt).rootMultiplicity 0 ≤
        (differences S (separator (j:K)) wt).rootMultiplicity 0 := by
  classical
  constructor
  · intro hi j _
    rw [(order_eq_diagonal_iff S _ wt positive).mpr hi]
    exact diagonal_le_order _ _ _
  · intro h
    obtain ⟨j,hj,hi⟩ := exists_bounded_separator S
    have best := h j (hj.trans bound)
    rw [(order_eq_diagonal_iff S _ wt positive).mpr hi] at best
    exact (order_eq_diagonal_iff S _ wt positive).mp (le_antisymm best (diagonal_le_order _ _ _))

#print axioms order_differences
#print axioms order_eq_diagonal_iff
#print axioms diagonal_le_order
#print axioms separates_iff_minimizes
end
end Sun28.Collision
