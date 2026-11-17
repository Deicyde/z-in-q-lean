import LandauDensity

namespace Sun28.PrimeModel
open Finset Filter Sun28.PrimeValues Sun28.PrimeMass Sun28.FinitePattern Sun28.SinglePrime
open Sun28.MixedSieve Sun28.ContactFactors Sun28.ContactSieve Sun28.WeightedSelection Sun28.MediumSieve
noncomputable section

/-- The finite sum over the actual fixed-prime upper moments. Rows and good
numerical scales may depend on the final cutoff. -/
def bonferroniRows (A : Fin 3→ℚ) (d K L : ℕ) (δ : ℝ) : Prop :=
  ∀ J : ℕ, ∃ j ≥ J, ∃ᶠ t : ℕ in atTop,
    let N:=lengthAt t
    let W:=rowWidth j N
    δ*((N:ℝ)*W) ≤ patternMass A d K K N W - ∑ p∈places K L, upperMoment A d K p N W

/-- The coefficient is allowed to decay along the cofinal cutoff sequence;
only its product with L log L must beat any prescribed tail constant. -/
def CofinalBonferroni : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0 < d → ∀ B : ℕ, ∃ K ≥ B,
      ∀ (m : ℕ) (D : ℝ), ∃ (L : ℕ) (δ : ℝ), max K m ≤ L ∧ 0 < δ ∧
        D < δ*((L:ℝ)*Real.log L) ∧ bonferroniRows (Sun28.RealPoleBounds.fixedScale n) d K L δ

theorem hybrid_of_bonferroni (inps : CofinalBonferroni) : HybridInputs := by
  intro X c q n roots d dp B
  obtain ⟨K,large,run⟩ := inps X c q n roots d dp B
  refine ⟨K,large,fun m D => ?_⟩
  obtain ⟨L,δ,le,pos,tail,rows⟩ := run m D
  refine ⟨L,δ,le,pos,tail,fun J => ?_⟩
  obtain ⟨j,jJ,good⟩ := rows J
  exact ⟨j,jJ,good.mono (fun _ h => h.trans (finite_moments _ _ _ _ _ _))⟩

/-- The earlier per-prime, same-row first moments imply a fixed positive
Bonferroni surplus for every L. This direction uses the summable local majorants. -/
theorem bonferroni_of_moments (inps : FirstMomentInputs) : CofinalBonferroni := by
  intro X c q n roots d dp B
  obtain ⟨K,α,bk,ap,rows⟩ := inps X c q n roots d dp (max B 2810)
  let A := Sun28.RealPoleBounds.fixedScale n
  have large : 2810 ≤ K := (le_max_right _ _).trans bk
  refine ⟨K,(le_max_left _ _).trans bk,fun m D => ?_⟩
  obtain ⟨r,hr⟩ := exists_nat_gt (Real.exp (4*D/α))
  let L := max (max K m) (max r 2)
  have rl : (r:ℝ) ≤ L := by exact_mod_cast (le_max_left r 2).trans (le_max_right _ _)
  have l2 : 2 ≤ L := (le_max_right r 2).trans (le_max_right _ _)
  have lp : 1 ≤ (L:ℝ) := by exact_mod_cast (show 1 ≤ L by omega)
  have logpos := Real.log_nonneg lp
  have lg := (Real.lt_log_iff_exp_lt (by linarith : 0 < (L:ℝ))).2 (hr.trans_le rl)
  have lo : D < (α/4)*Real.log L := by
    have := (div_lt_iff₀ ap).1 lg
    linarith
  refine ⟨L,α/4,le_max_left _ _,by positivity,lo.trans_le ?_,fun J => ?_⟩
  · exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left logpos lp) (by positivity)
  obtain ⟨j,jJ,lower,upper⟩ := rows J
  let P:=places K L
  let ε:=α/(4*((P.card:ℝ)+1))
  have ep : 0 < ε := by dsimp [ε]; positivity
  have slack : (P.card:ℝ)*ε ≤ α/4 := by
    dsimp [ε]
    calc
      _ ≤ ((P.card:ℝ)+1)*(α/(4*((P.card:ℝ)+1))) := by
        apply mul_le_mul_of_nonneg_right (by linarith)
        positivity
      _ = _ := by field_simp
  have together : ∀ᶠ t : ℕ in atTop, ∀ p∈P,
        upperMoment A d K p (lengthAt t) (rowWidth j (lengthAt t)) ≤
          1404/((p:ℝ)-1)^2 * patternMass A d K K (lengthAt t) (rowWidth j (lengthAt t)) +
          ε*((lengthAt t:ℝ)*rowWidth j (lengthAt t)) :=
    (Filter.eventually_all_finset P).2 fun p hp => upper p (mem_places.mp hp).2.2 (mem_places.mp hp).1 ε ep
  refine ⟨j,jJ,(lower.and_eventually together).mono (fun t good => ?_)⟩
  let N:=lengthAt t
  let W:=rowWidth j N
  let M:=patternMass A d K K N W
  let Z:ℝ:=(N:ℝ)*W
  let f:=fun p:ℕ=>1404/((p:ℝ)-1)^2
  have loM : α*Z ≤ M := good.1
  have non : 0 ≤ M := sum_nonneg (fun z _ => base_nonneg A K z)
  have cap : (∑ p∈P,f p) ≤ 1/2 := uniform_sum P f
    (fun p hp => large.trans (mem_places.mp hp).1.le) (fun _ _ => le_rfl)
  have lim : ∑ p∈P, upperMoment A d K p N W ≤ (1/2)*M+(α/4)*Z := calc
    _ ≤ ∑ p∈P, (f p*M+ε*Z) := sum_le_sum good.2
    _ = (∑ p∈P,f p)*M+((P.card:ℝ)*ε)*Z := by
      rw [sum_add_distrib, sum_mul, sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right cap non)
      (mul_le_mul_of_nonneg_right slack (by dsimp [Z]; positivity))
  change (α/4)*Z ≤ M - ∑ p∈P, upperMoment A d K p N W
  linarith

end
end Sun28.PrimeModel
#print axioms Sun28.PrimeModel.hybrid_of_bonferroni
#print axioms Sun28.PrimeModel.bonferroni_of_moments
