import CollisionCounts

set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace Sun28.MixedSieve
open Finset
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic prime positions modulo p for a residue pair (u,w). -/
def norms (c : ι→F p) (u w : F p) (i : ι) : F p := u+c i*w^2

noncomputable def obstructed (t : ι→F p) : Finset ((i : ι)→Circle p (t i)) :=
  univ.biUnion fun ij : ι × ι => Fintype.piFinset (pairSets t ij.1 ij.2)

/-- Exactly the ordered mixed collisions, including a collision of a shift with itself. -/
theorem obstructed_iff {t : ι→F p} (z : (i : ι)→Circle p (t i)) :
    z∈obstructed t ↔ ∃ i j,z i∈bad p (t i) true ∧ z j∈bad p (t j) false := by
  constructor
  · intro h
    obtain ⟨⟨i,j⟩,_,h⟩:=Finset.mem_biUnion.mp h
    exact ⟨i,j,(pairSets_mem t i j z).mp h⟩
  · rintro ⟨i,j,h⟩
    exact Finset.mem_biUnion.mpr ⟨(i,j),mem_univ _,(pairSets_mem t i j z).mpr h⟩

/-- Restrict to unit norm residues, as in the abelian part of the Artin density. -/
noncomputable def loss (c : ι→F p) (u w : F p) : ℝ := by
  classical
  let t:=norms c u w
  exact if ∀ i,t i≠0 then ((obstructed t).card:ℝ)/Fintype.card ((i : ι)→Circle p (t i)) else 0

private theorem sum_cap {t : ι→F p} : ((obstructed t).card:ℝ)/Fintype.card ((i : ι)→Circle p (t i)) ≤
    ∑ ij : ι×ι,pairMass t ij.1 ij.2 := by
  classical
  simp only [pairMass,boxMass]
  rw [←Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have bound : (obstructed t).card ≤ ∑ ij : ι×ι,(Fintype.piFinset (pairSets t ij.1 ij.2)).card :=
    Finset.card_biUnion_le
  exact_mod_cast bound


private theorem point_bound (hp : 2<p) (c : ι→F p) (u w : F p) :
    loss c u w ≤ ∑ ij : ι×ι,
      ((2/((p:ℝ)-1))^2 + (if ij.1=ij.2 ∧ norms c u w ij.1= -1 then 2/((p:ℝ)-1) else 0)) := by
  classical
  have pos : 0≤2/((p:ℝ)-1) := by
    have d : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
    exact div_nonneg (by norm_num) (by linarith)
  dsimp only [loss]
  split
  next hz =>
    apply sum_cap.trans
    apply Finset.sum_le_sum
    rintro ⟨i,j⟩ _
    dsimp only
    by_cases same : i=j
    · subst j
      simpa using (diagonal hp _ hz i).trans (le_add_of_nonneg_left (sq_nonneg (2/((p:ℝ)-1))))
    · simpa [same] using offdiag hp _ hz same
  next _ =>
    apply Finset.sum_nonneg
    intro ij _
    split <;> positivity

/-- Sum in u first. For fixed w and i the diagonal norm -1 occurs exactly once. -/
theorem exceptional_sum (c : ι→F p) (w : F p) (a : ℝ) :
    (∑ u : F p,∑ ij : ι×ι, if ij.1=ij.2 ∧ norms c u w ij.1= -1 then a else 0)
    = Fintype.card ι*a := by
  classical
  rw [Finset.sum_comm]
  have one (i j : ι) :
      (∑ u : F p, if i=j ∧ norms c u w i= -1 then a else 0) = if i=j then a else 0 := by
    by_cases eq : i=j
    · subst j
      have e (u : F p) : norms c u w i= -1 ↔ u= -1-c i*w^2 := by
        simp only [norms]; constructor <;> intro h <;> linear_combination h
      simp [e]
    · simp [eq]
  simp_rw [one]
  rw [Fintype.sum_prod_type]
  simp

/-- The loss in the joint local density, averaged over all ordinary residue pairs.
It is normalized by p² before restriction to unit patterns. -/
noncomputable def averageLoss (c : ι→F p) : ℝ :=
  (∑ w : F p,∑ u : F p,loss c u w)/((p:ℝ)^2)

theorem average_bound (hp : 2<p) (c : ι→F p) :
    averageLoss c ≤ (Fintype.card ι:ℝ)^2*(2/((p:ℝ)-1))^2
      + (Fintype.card ι:ℝ)*(2/((p:ℝ)-1))/(p:ℝ) := by
  classical
  have pos : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  let a : ℝ:=2/((p:ℝ)-1)
  have row (w : F p) : (∑ u : F p,loss c u w)≤(p:ℝ)*(Fintype.card ι:ℝ)^2*a^2+Fintype.card ι*a := by
    calc
      _ ≤ ∑ u : F p, ∑ ij : ι×ι,(a^2+if ij.1=ij.2 ∧ norms c u w ij.1= -1 then a else 0) :=
        Finset.sum_le_sum fun u _ => point_bound hp c u w
      _ = _ := by simp_rw [Finset.sum_add_distrib]; rw [exceptional_sum]; simp [Fintype.card_prod]; ring
  unfold averageLoss
  apply (div_le_iff₀ (sq_pos_of_pos pos)).mpr
  calc
    _ ≤ ∑ _ : F p, ((p:ℝ)*(Fintype.card ι:ℝ)^2*a^2+Fintype.card ι*a) := Finset.sum_le_sum fun w _ => row w
    _ = _ := by simp [ZMod.card,a]; field_simp

end Sun28.MixedSieve
#print axioms Sun28.MixedSieve.obstructed_iff
#print axioms Sun28.MixedSieve.exceptional_sum
#print axioms Sun28.MixedSieve.average_bound
