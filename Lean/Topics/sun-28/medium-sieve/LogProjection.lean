import LogCutoffTransfer

namespace Sun28.MediumSieve
open Sun28.SinglePrime Sun28.ContactFactors Sun28.SieveTail Sun28.WeightedSelection Sun28.ContactSieve
open Sun28.Ordinary Sun28.HeightFibres Sun28.HeightFibres.Sharp
noncomputable section

/-- Include all primes dividing the denominator dilation or a difference of distinct shifts in the base. -/
def exceptionalBound (A : Fin 3→ℚ) (d : ℕ) :=
  max d (Finset.univ.sup fun z : ↥(shifts A)×↥(shifts A)=>(gap z.1 z.2).natAbs)

theorem outside_base {A : Fin 3→ℚ} {d K p : ℕ} (positive : 0<d) (base : exceptionalBound A d≤K)
    (above : K<p) (i j : ↥(shifts A)) (different : gap i j≠0) :
    ¬p∣d ∧ ¬p∣(gap i j).natAbs := by
  have first : d≤K := (le_max_left _ _).trans base
  have second : (gap i j).natAbs≤K :=
    (Finset.le_sup (f:=fun z : ↥(shifts A)×↥(shifts A)=>(gap z.1 z.2).natAbs) (Finset.mem_univ (i,j))).trans
      ((le_max_right _ _).trans base)
  exact ⟨fun h => above.not_ge ((Nat.le_of_dvd positive h).trans first),
    fun h => above.not_ge ((Nat.le_of_dvd (Int.natAbs_pos.mpr different) h).trans second)⟩

/-- The finite asymptotics and the upper sieve now concern only polylogarithmic obstruction primes. -/
structure LogBounds (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ : ℕ) : Prop where
  estimates : ∃ (K : ℕ) (σ C : ℝ),2810≤K ∧ exceptionalBound A d≤K ∧
    (∀ p∈T,p≤K) ∧ (∀ p∈κ.primeFactors,p≤K) ∧ 0<σ ∧ 0≤C ∧
    ∀ L : ℕ,K≤L → CountThreshold A d H Y T κ K L σ ∧ ∃ J,LogRow A d H Y T κ L J C

def LogInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ),AdmissibleRoots X c q n →
    ∀ (d κ : ℕ) (T : Finset ℕ),0<d → 0<κ → (∀ p∈T,p.Prime) → 2∈T →
      ∀ H Y : ℝ,LogBounds (Sun28.RealPoleBounds.fixedScale n) d H Y T κ

theorem log_positive_surplus (input : LogInputs) : PositiveSurplus := by
  intro X c q n roots d κ T dp kp primes two H Y
  obtain ⟨K,σ,C,big,_,inT,inAux,sp,_,est⟩:=(input X c q n roots d κ T dp kp primes two H Y).estimates
  obtain ⟨m,hm⟩:=exists_nat_gt (8*C/σ)
  let L:=max K m
  have kl : K≤L := le_max_left ..
  have ml : m≤L := le_max_right ..
  have lp : 0<(L:ℝ) := by exact_mod_cast (by omega : 0<L)
  have step : C/(L:ℝ)<σ/8 := by
    have h := (div_lt_iff₀ sp).mp (hm.trans_le (by exact_mod_cast ml : (m:ℝ)≤L))
    apply (div_lt_iff₀ lp).mpr;nlinarith only [h]
  obtain ⟨finite,J,middle⟩:=est L kl
  exact ⟨L,log_surplus finite middle big kl inT inAux sp step⟩

theorem fixed_projection_log (realCurves : RealComponents.PublishedProposition72)
    (units : FiveMarkUnits.PublishedCorollary72) (pell : PublishedPell312)
    (regulator : Regulator35) (characters : QuadraticCharacterDiscriminants)
    (height : Deep) (counts : LogInputs) (points : TwistRank.LocalResidual) (x : ℚ) :
    (∃ w : Fin 28→ℚ,eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ,x=(z:ℚ) := by
  have original := (original_iff_published_deep units pell regulator characters).mpr height
  exact TwistRank.fixed_projection realCurves units (FiveDescent.glazer_iff_twist.mp original)
    (log_positive_surplus counts) points x

end
end Sun28.MediumSieve
#print axioms Sun28.MediumSieve.outside_base
#print axioms Sun28.MediumSieve.log_positive_surplus
#print axioms Sun28.MediumSieve.fixed_projection_log
