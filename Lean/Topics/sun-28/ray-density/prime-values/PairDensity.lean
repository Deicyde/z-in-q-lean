import HybridCriterion

namespace Sun28.PrimeValues
open Sun28.MixedSieve Sun28.PrimeLower Sun28.ContactFactors Finset
open scoped Classical
noncomputable section
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sum over ordered pairs, before overlaps between distinct pairs are removed. -/
def fibrePairs (c : ι→F p) (u w:F p) : ℝ :=
  if ∀i,norms c u w i≠0 then ∑ij : ι×ι,pairMass (norms c u w) ij.1 ij.2 else 0

def averagePairs (c:ι→F p) : ℝ :=
  (∑ w : F p,∑ u : F p,fibrePairs c u w)/((p:ℝ)^2)

theorem fibre_point_bound (hp : 2<p) (c : ι→F p) (u w : F p) :
    fibrePairs c u w ≤ ∑ ij : ι×ι,
      ((2/((p:ℝ)-1))^2 + (if ij.1=ij.2 ∧ norms c u w ij.1= -1 then 2/((p:ℝ)-1) else 0)) := by
  have pos : 0≤2/((p:ℝ)-1) := by
    have d : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
    exact div_nonneg (by norm_num) (by linarith)
  unfold fibrePairs
  split
  next hz =>
    apply Finset.sum_le_sum
    rintro ⟨i,j⟩ _
    dsimp only
    by_cases same : i=j
    · subst j
      simpa using (diagonal hp _ hz i).trans (le_add_of_nonneg_left (sq_nonneg (2/((p:ℝ)-1))))
    · simpa [same] using offdiag hp _ hz same
  next => apply sum_nonneg;intro ij _;split <;> positivity

theorem averaged_pairs (hp : 2<p) (c : ι→F p) :
    averagePairs c ≤ (Fintype.card ι:ℝ)^2*(2/((p:ℝ)-1))^2
      + (Fintype.card ι:ℝ)*(2/((p:ℝ)-1))/(p:ℝ) := by
  have pos : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
  let a : ℝ:=2/((p:ℝ)-1)
  have row (w : F p) : (∑ u : F p,fibrePairs c u w)≤(p:ℝ)*(Fintype.card ι:ℝ)^2*a^2+Fintype.card ι*a := by
    calc
      _ ≤ ∑ u : F p, ∑ ij : ι×ι,(a^2+if ij.1=ij.2 ∧ norms c u w ij.1= -1 then a else 0) :=
        sum_le_sum fun u _ => fibre_point_bound hp c u w
      _ = _ := by simp_rw [Finset.sum_add_distrib]; rw [exceptional_sum]; simp [Fintype.card_prod]; ring
  unfold averagePairs
  apply (div_le_iff₀ (sq_pos_of_pos pos)).mpr
  calc
    _ ≤ ∑ _ : F p, ((p:ℝ)*(Fintype.card ι:ℝ)^2*a^2+Fintype.card ι*a) := sum_le_sum fun w _=>row w
    _ = _ := by simp [ZMod.card,a];field_simp

theorem relative_pair_rate (hp : 26≤p) (hk : Fintype.card ι≤13) (c : ι→F p) :
    averagePairs c/unitRate c ≤ 1404/((p:ℝ)-1)^2 := by
  have P : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have Q : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
  have half := (inert_relative_loss_le c (by omega)).1
  have up : 0<unitRate c := by linarith
  have capped : (Fintype.card ι:ℝ) ≤ 13 := by exact_mod_cast hk
  have quad := mul_self_le_mul_self (Nat.cast_nonneg (Fintype.card ι) : (0:ℝ)≤Fintype.card ι) capped
  have C : 8*(Fintype.card ι:ℝ)^2+4*Fintype.card ι ≤ 1404 := by nlinarith
  have b := averaged_pairs (by omega : 2<p) c
  apply (div_le_iff₀ up).mpr
  calc
    _ ≤ _ := b
    _ ≤ (8*(Fintype.card ι:ℝ)^2+4*Fintype.card ι)/((p:ℝ)-1)^2*(1/2) := by
      field_simp [P.ne',sub_ne_zero.mpr Q.ne']
      nlinarith [show 0≤(Fintype.card ι:ℝ)*((p:ℝ)-1) by positivity]
    _ ≤ 1404/((p:ℝ)-1)^2*unitRate c :=
      mul_le_mul (div_le_div_of_nonneg_right C (sq_nonneg _)) half (by norm_num) (by positivity)

end
end Sun28.PrimeValues
#print axioms Sun28.PrimeValues.fibre_point_bound
#print axioms Sun28.PrimeValues.averaged_pairs
#print axioms Sun28.PrimeValues.relative_pair_rate
