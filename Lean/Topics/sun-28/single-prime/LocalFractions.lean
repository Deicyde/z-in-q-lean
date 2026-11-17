import RayRectangles

namespace Sun28.SinglePrime
open Finset Sun28.MixedSieve
open scoped Classical
noncomputable section
inductive Test | plus | minus | both deriving DecidableEq

def accepts (P M : Prop) : Test→Prop
  | .plus => P
  | .minus => M
  | .both => P ∧ M

/-- The set of Gaussian tuples satisfying the given coordinate rectangle. -/
def rectangle {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : Test) (t : ι→F p) : Finset ((i : ι)→Circle p (t i)) :=
  match j with
  | .plus => safeBox t true
  | .minus => safeBox t false
  | .both => safeBox t true ∩ safeBox t false

theorem rectangle_card {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : Test) (t : ι→F p) :
    (rectangle j t).card=∏ i,(univ.filter fun z : Circle p (t i) =>
      accepts (z∉bad p (t i) true) (z∉bad p (t i) false) j).card := by
  let coord (i : ι) : Finset (Circle p (t i)) :=
    univ.filter fun z => accepts (z∉bad p (t i) true) (z∉bad p (t i) false) j
  have mem (i : ι) (x : Circle p (t i)) :
      x∈coord i ↔ accepts (x∉bad p (t i) true) (x∉bad p (t i) false) j := by
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x))
  have h : rectangle j t=Fintype.piFinset coord := by
    ext z
    rw [Fintype.mem_piFinset]
    simp_rw [mem]
    cases j <;> simp [rectangle,safeBox,accepts,forall_and]
  rw [h,Fintype.card_piFinset]

def fraction {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : Test) (t : ι→F p) : ℝ :=
  ((rectangle j t).card:ℝ)/Fintype.card ((i:ι)→Circle p (t i))

theorem fractions_at_norms {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι→F p) (unit : ∀ i,t i≠0) :
    1-((((obstructed t).card:ℝ)/Fintype.card ((i:ι)→Circle p (t i)))) =
      fraction .plus t+fraction .minus t-fraction .both t := by
  have pos : 0<Fintype.card ((i:ι)→Circle p (t i)) := by
    apply Fintype.card_pos_iff.mpr
    refine ⟨fun i => rotate (unit i) ⟨(1,0),by simp⟩⟩
  have hs : (obstructed t)ᶜ=safeBox t true ∪ safeBox t false := by
    ext z
    exact (Finset.mem_compl.trans (good_iff_union t z))
  have hu := Finset.card_union_add_card_inter (safeBox t true) (safeBox t false)
  rw [←hs,Finset.card_compl] at hu
  have le := Finset.card_le_univ (obstructed t)
  have h : (Fintype.card ((i:ι)→Circle p (t i)):ℝ)-(obstructed t).card+
      (safeBox t true ∩ safeBox t false).card=(safeBox t true).card+(safeBox t false).card := by
    exact_mod_cast hu
  unfold fraction
  simp only [rectangle]
  field_simp [Nat.cast_ne_zero.mpr pos.ne']
  linarith only [h]

def averageBox {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι→F p) (j : Test) : ℝ :=
  (∑ w : F p, ∑ u : F p,if ∀ i,norms c u w i≠0 then fraction j (norms c u w) else 0)/(p:ℝ)^2

theorem signed_average {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι→F p) :
    unitRate c-averageLoss c=averageBox c .plus+averageBox c .minus-averageBox c .both := by
  let I (u w : F p) : ℝ := if ∀ i,norms c u w i≠0 then 1 else 0
  let R (j : Test) (u w : F p) : ℝ := if ∀ i,norms c u w i≠0 then fraction j (norms c u w) else 0
  have point (u w : F p) : I u w-loss c u w=R .plus u w+R .minus u w-R .both u w := by
    by_cases ok : ∀ i,norms c u w i≠0
    · simpa only [I,R,loss,ite_eq_left ok] using fractions_at_norms (norms c u w) ok
    · simp [I,R,loss,ok]
  have sums := congrArg (fun f : F p→F p→ℝ => ∑ w,∑ u,f u w) (funext fun u=>funext fun w=>point u w)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at sums
  change (∑ w,∑ u,I u w)/(p:ℝ)^2-(∑ w,∑ u,loss c u w)/(p:ℝ)^2=
    (∑ w,∑ u,R .plus u w)/(p:ℝ)^2+(∑ w,∑ u,R .minus u w)/(p:ℝ)^2-(∑ w,∑ u,R .both u w)/(p:ℝ)^2
  rw [←sub_div,←add_div,←sub_div,sums]

/-- The three conditional rectangle proportions for the cleared prime polynomial. -/
def localProportion (A : Fin 3→ℚ) (p : ℕ) (j : Test) : ℝ :=
  if h : p.Prime then
    let _ : Fact p.Prime:=⟨h⟩
    averageBox (coefficients A p) j / unitRate (coefficients A p)
  else 0

theorem signed_local (A : Fin 3→ℚ) (p : ℕ) (prime : p.Prime) (large : 2810≤p) :
    localProportion A p .plus+localProportion A p .minus-localProportion A p .both=1-markedLoss A p := by
  let _ : Fact p.Prime:=⟨prime⟩
  let c:=coefficients A p
  have hk : Fintype.card ↥(Sun28.ContactFactors.shifts A)≤13 := by simpa using Sun28.GaussianSelection.shifts_card_le A
  have cap : (Fintype.card ↥(Sun28.ContactFactors.shifts A):ℝ)<(p:ℝ) := by exact_mod_cast (show Fintype.card _<p by omega)
  have pos := prime.pos
  have frac : (Fintype.card ↥(Sun28.ContactFactors.shifts A):ℝ)/p<1 :=
    (div_lt_one (by exact_mod_cast pos)).mpr cap
  have up := units_lower c
  have non : unitRate c≠0 := by linarith
  simp only [localProportion,prime,reduceDIte,markedLoss,relativeLoss]
  change averageBox c .plus/unitRate c+averageBox c .minus/unitRate c-averageBox c .both/unitRate c=1-averageLoss c/unitRate c
  rw [←add_div,←sub_div,←signed_average]
  field_simp

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.rectangle_card
#print axioms Sun28.SinglePrime.fractions_at_norms
#print axioms Sun28.SinglePrime.signed_average
#print axioms Sun28.SinglePrime.signed_local
