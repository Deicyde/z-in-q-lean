import RationalProjection

/-! Equality tests by one auxiliary polynomial indeterminate and selection of a separating value. -/
open Polynomial Finset
namespace ZInQBlueprint.SunTower
noncomputable section
variable {L ι : Type*} [Field L]

/-- At a candidate value t, keep the perturbation U formal. Positive exponents accommodate the
local lengths of a possibly nonreduced fiber in a characteristic polynomial. -/
def resolvent (S : Finset ι) (ell f : ι → L) (mult : ι → ℕ) (t : L) : L[X] :=
  ∏ x ∈ S, (C (t - ell x) - C (f x) * X) ^ mult x

private theorem linear_zero (a c : L) : C a - C c * X = 0 ↔ a=0 ∧ c=0 := by
  constructor
  · intro h
    have ha := congrArg (fun p : L[X] => p.eval 0) h
    have hc := congrArg (fun p : L[X] => p.eval 1) h
    simp only [eval_sub,eval_mul,eval_C,eval_X,eval_zero,mul_zero,sub_zero] at ha
    simp only [eval_sub,eval_mul,eval_C,eval_X,eval_zero,mul_one,ha,zero_sub,neg_eq_zero] at hc
    exact ⟨ha,hc⟩
  · rintro ⟨rfl,rfl⟩; simp

/-- A resolvent is the zero polynomial in U exactly when at least one geometric tuple
above t satisfies f=0. This holds for arbitrary positive multiplicities. -/
theorem resolvent_zero_iff (S : Finset ι) (ell f : ι → L) (mult : ι → ℕ)
    (hm : ∀ x ∈ S, 0 < mult x) (t : L) :
    resolvent S ell f mult t = 0 ↔ ∃ x ∈ S, ell x = t ∧ f x = 0 := by
  unfold resolvent
  rw [Finset.prod_eq_zero_iff]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  rw [pow_eq_zero_iff (hm x hx).ne',linear_zero,sub_eq_zero]
  exact and_congr eq_comm Iff.rfl

/-- The degree in U is bounded by the total length, including fibers where the
specialization of a factor is the zero polynomial. -/
theorem resolvent_degree (S : Finset ι) (ell f : ι → L) (mult : ι → ℕ) (t : L) :
    (resolvent S ell f mult t).natDegree ≤ ∑ x ∈ S, mult x := by
  unfold resolvent
  apply (Polynomial.natDegree_prod_le ..).trans
  apply Finset.sum_le_sum
  intro x hx
  have hlin : (C (t-ell x) - C (f x)*X).natDegree ≤ 1 :=
    (natDegree_sub_le ..).trans (max_le (by simp) ((natDegree_C_mul_le ..).trans (by simp)))
  calc
    _ = mult x * (C (t-ell x) - C (f x)*X).natDegree := natDegree_pow _ _
    _ ≤ mult x*1 := Nat.mul_le_mul_left _ hlin
    _ = _ := Nat.mul_one _

/-- Fixing an upper bound for the length gives a finite coefficient or evaluation test.
All d+1 integer substitutions vanish if and only if the whole U-polynomial vanishes. -/
theorem resolvent_samples_iff [CharZero L] (S : Finset ι) (ell f : ι → L) (mult : ι → ℕ)
    (t : L) {d : ℕ} (hd : (∑ x ∈ S, mult x) ≤ d) :
    (∀ j : ℕ, j ≤ d → (resolvent S ell f mult t).eval (j:L) = 0) ↔
      resolvent S ell f mult t = 0 := by
  classical
  constructor
  · intro h
    by_contra hn
    let inc : ℕ ↪ L := ⟨Nat.cast,Nat.cast_injective⟩
    let H := (Finset.range (d+1)).map inc
    have sub : H.val ⊆ (resolvent S ell f mult t).roots := by
      intro z hz
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp (show z ∈ H from hz)
      exact (mem_roots hn).mpr (h j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    have impossible := (card_le_degree_of_subset_roots sub).trans ((resolvent_degree S ell f mult t).trans hd)
    simp [H] at impossible
  · intro hz j hj
    rw [hz,eval_zero]

/-- At a separated value the coefficients of the resolvent test that tuple alone. -/
theorem resolvent_at_separated (S : Finset ι) (ell f : ι → L) (mult : ι → ℕ)
    (hm : ∀ x ∈ S, 0 < mult x) (hi : Set.InjOn ell (S : Set ι)) {x : ι} (hx : x ∈ S) :
    resolvent S ell f mult (ell x) = 0 ↔ f x = 0 := by
  rw [resolvent_zero_iff S ell f mult hm]
  constructor
  · rintro ⟨y,hy,he,hf⟩
    exact hi hy hx he ▸ hf
  · exact fun hf => ⟨x,hx,rfl,hf⟩

/-- Count the distinct roots of the geometric characteristic polynomial, ignoring multiplicities. -/
def distinctValues [DecidableEq L] {n : ℕ} (S : Finset (Fin n → L)) (b : ℕ) : ℕ :=
  (S.image (separator (b:L))).card

/-- Maximizing the number of distinct projected values on the bounded list suffices
to select a separator; the number of geometric tuples need not be known in advance. -/
theorem separating_iff_maximizes [DecidableEq L] [CharZero L] {n : ℕ} (S : Finset (Fin n → L))
    {b B : ℕ} (hB : S.card.choose 2*(n-1) ≤ B) :
    Set.InjOn (separator (b:L)) (S : Set (Fin n → L)) ↔
      ∀ j : ℕ, j ≤ B → distinctValues S j ≤ distinctValues S b := by
  rw [← Finset.card_image_iff]
  change distinctValues S b = S.card ↔ _
  constructor
  · intro hi j hj
    rw [hi]
    exact Finset.card_image_le
  · intro hm
    obtain ⟨j,hj,hs⟩ := exists_bounded_separator S
    have hc : distinctValues S j = S.card := Finset.card_image_of_injOn hs
    exact le_antisymm Finset.card_image_le (hc ▸ hm j (hj.trans hB))

/-- The polynomial with one linear factor per distinct value has degree exactly that count. -/
theorem reduced_projection_degree [DecidableEq L] {n : ℕ} (S : Finset (Fin n → L)) (b : ℕ) :
    (∏ t ∈ S.image (separator (b:L)), ((X : L[X])-C t)).natDegree = distinctValues S b := by
  exact natDegree_finsetProd_X_sub_C_eq_card _ id

end
end ZInQBlueprint.SunTower
#print axioms ZInQBlueprint.SunTower.resolvent_zero_iff
#print axioms ZInQBlueprint.SunTower.resolvent_degree
#print axioms ZInQBlueprint.SunTower.resolvent_samples_iff
#print axioms ZInQBlueprint.SunTower.resolvent_at_separated
#print axioms ZInQBlueprint.SunTower.separating_iff_maximizes
#print axioms ZInQBlueprint.SunTower.reduced_projection_degree
