import FlagApplication

namespace Sun28.ConeFibres
open Sun28.ContactFactors Sun28.MediumSieve
noncomputable section

private def model (q k e : ℝ) :=
  let n := q+(q-1)*e
  (1-1/q^3)*((q-1)*(q-e)*(2*n+(k-2)*(q-e))+n^2-1)/(q^4-1)

private def num (s : Bool) (q k : ℝ) := if s then
    3*k*q^4+2*k*q^2-2*k*q+k+2*q^3+4*q^2+2*q
  else k*q^3-k*q^2-k*q-k+2*q^2+2*q

private def den (s : Bool) (q : ℝ) :=
  if s then q*(q+1)*(q^2+1) else q*(q^2+1)

private theorem numerator_bound (s : Bool) (q k : ℝ) (hq : 3≤q) (hk : 0≤k) (cap : k≤13) :
    |num s q k| ≤ 50*den s q := by
  let u := q-3
  have hu : 0≤u := sub_nonneg.mpr hq
  have qu : q=u+3 := by dsimp [u]; ring
  refine abs_le.mpr ⟨?_,?_⟩
  · apply sub_nonneg.mp
    rw [qu]
    cases s <;> dsimp [num,den] <;> ring_nf <;> positivity
  · let l := 13-k
    have hl : 0≤l := sub_nonneg.mpr cap
    have kl : k=13-l := by dsimp [l]; ring
    apply sub_nonneg.mp
    rw [qu,kl]
    cases s <;> dsimp [num,den] <;> ring_nf <;> positivity

private theorem model_error (s : Bool) (q k : ℝ) (hq : 3≤q) (hk : 0≤k) (cap : k≤13) :
    let e : ℝ := if s then 1 else -1
    |model q k e - (k+2*e)/q|≤50/q^2 := by
  dsimp only
  have qp : 0<q := by linarith
  have q4 : 0<q^4-1 := by nlinarith only [hq,sq_nonneg (q-1),sq_nonneg (q^2-1)]
  have dp : 0<den s q := by cases s <;> dsimp [den] <;> positivity
  have eq : (model q k (if s then 1 else -1)-(k+2*(if s then 1 else -1))/q)*q^2 =
      (if s then -num s q k else num s q k)/den s q := by
    cases s <;> dsimp [model,num,den] <;>
      field_simp [ne_of_gt q4,ne_of_gt qp] <;> ring
  apply (le_div_iff₀ (sq_pos_of_pos qp)).mpr
  rw [←abs_of_nonneg (sq_nonneg q),←abs_mul,eq,abs_div,abs_of_pos dp]
  apply (div_le_iff₀ dp).mpr
  cases s <;> simpa only [Bool.false_eq_true,ite_false,ite_true,abs_neg] using numerator_bound _ q k hq hk cap

def fullDensity {A : Fin 3→ℚ} (p : ℕ) [Fact p.Prime] (i j : ↥(shifts A)) : ℝ :=
  (1-1/(p:ℝ)^3)*((actualFlag p i j).card:ℝ)/((p:ℝ)^4-1)

theorem chi_mod_four {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    chi p = if p%4=1 then 1 else -1 := by
  rw [chi,legendreSym.at_neg_one odd,ZMod.χ₄_nat_eq_if_mod_four]
  simp [(Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).mpr odd]

theorem full_density_error {A : Fin 3→ℚ} {p d : ℕ} [Fact p.Prime] (pos : 0<d)
    (large : exceptionalBound A d<p) (odd : p≠2) (i j : ↥(shifts A)) (diff : i≠j) :
    |fullDensity p i j - (((shifts A).card:ℝ)+2*(chi p:ℝ))/p| ≤ 50/(p:ℝ)^2 := by
  let k := (shifts A).card
  have hq : (3:ℝ)≤p := by
    have h := (Fact.out : p.Prime).two_le
    exact_mod_cast (by omega : 3≤p)
  have hk : (0:ℝ)≤k := Nat.cast_nonneg _
  have cap : (k:ℝ)≤13 := by exact_mod_cast Sun28.GaussianSelection.shifts_card_le A
  have count : ((actualFlag p i j).card:ℝ)=(flagPolynomial p k:ℝ) := by
    exact_mod_cast actual_flag_card_above pos large odd i j diff
  have eq : fullDensity p i j=model p k (chi p) := by
    unfold fullDensity model
    rw [count]
    unfold flagPolynomial zeroNorm
    push_cast
    rfl
  rw [eq,chi_mod_four odd]
  by_cases split : p%4=1
  · simpa [split,k] using model_error true p k hq hk cap
  · simpa [split,k] using model_error false p k hq hk cap

theorem full_density_error_mod_four {A : Fin 3→ℚ} {p d : ℕ} [Fact p.Prime] (pos : 0<d)
    (large : exceptionalBound A d<p) (odd : p≠2) (i j : ↥(shifts A)) (diff : i≠j) :
    |fullDensity p i j - (if p%4=1 then ((shifts A).card:ℝ)+2 else ((shifts A).card:ℝ)-2)/p|
    ≤ 50/(p:ℝ)^2 := by
  have e:=full_density_error pos large odd i j diff
  rw [chi_mod_four odd] at e
  by_cases h : p%4=1
  · simpa [h] using e
  · simpa [h,sub_eq_add_neg] using e

end
end Sun28.ConeFibres
#print axioms Sun28.ConeFibres.chi_mod_four
#print axioms Sun28.ConeFibres.full_density_error
#print axioms Sun28.ConeFibres.full_density_error_mod_four
