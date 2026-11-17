import AcceptedMass

namespace Sun28.CommonRows
open Finset Filter Sun28.PrimeValues Sun28.FinitePattern Sun28.PrimeClasses
open Sun28.PrimeLower Sun28.ContactFactors Sun28.ContactSieve Sun28.WeightedSelection
open Sun28.SinglePrime Sun28.MediumSieve Sun28.MixedSieve Sun28.PrimeMass
open scoped Classical
noncomputable section

/-- A lower criterion that can use a single chosen pair of distinct additional
places. Their intersection is added back to the exact one-place charges. -/
def PairCorrectedInputs : Prop :=
  ∀ (X c q:ℤ) (n:Fin 4→ℤ), AdmissibleRoots X c q n →
    ∀d:ℕ,0<d → ∀B:ℕ,∃K≥B,∀(m:ℕ)(D:ℝ),∃(L:ℕ)(δ:ℝ),
      max K m≤L ∧ 0<δ ∧ D<δ*((L:ℝ)*Real.log L) ∧
      ∀J:ℕ,∃j≥J,∃ᶠ t:ℕ in atTop,
        let A:=Sun28.RealPoleBounds.fixedScale n
        let N:=lengthAt t
        let W:=rowWidth j N
        let Z:=(N:ℝ)*W
        let M:=patternMass A d K K N W-∑p∈places K L,onePlaceMass A d K N W p
        δ*Z≤M ∨ ∃p∈places K L,∃q∈places K L,p≠q ∧
            δ*Z≤M+moment A d K N W (fun z=>signedHit A p z ∧ signedHit A q z)

theorem positive_surplus (lower:PairCorrectedInputs) (upper:PrimeUpperInputs) : PositiveSurplus := by
  intro X c q n roots d κ T dp kp primes two H Y
  obtain ⟨K₁,C,cn,upp⟩:=upper X c q n roots d κ T dp kp primes two H Y
  let A:=Sun28.RealPoleBounds.fixedScale n
  let B:=max 7 (max (T.sup id) (κ.primeFactors.sup id))
  obtain ⟨K,bk,lower⟩:=lower X c q n roots d dp B
  obtain ⟨L,δ,large,δp,margin,counts⟩:=lower K₁ (2*(C*(4*Real.log 4)))
  have kl:K≤L:=(le_max_left K K₁).trans large
  have k7:7≤K:=(le_max_left _ _).trans bk
  have l2:2≤L:=by omega
  have lp:0<(L:ℝ):=by exact_mod_cast (show 0<L by omega)
  have logp:=Real.log_pos (show (1:ℝ)<L by exact_mod_cast (show 1<L by omega))
  obtain ⟨J,row⟩:=upp L ((le_max_right _ _).trans large)
  have inT (p:ℕ) (hp:p∈T):p≤K:=(le_sup (f:=id) hp).trans ((le_max_left _ _).trans ((le_max_right _ _).trans bk))
  have inAux (p:ℕ) (hp:p∈κ.primeFactors):p≤K:=(le_sup (f:=id) hp).trans ((le_max_right _ _).trans ((le_max_right _ _).trans bk))
  obtain ⟨I,fit⟩:=fixed_rows (P:=fun N W=>cleanMass A d K L N W≤
      mainMass T κ L (box (A:=A) (d:=d) (H:=H) (Y:=Y) N W))
    (fun w short=>eventually_clean_le_main k7 inT inAux w short)
  have rows (JJ:ℕ) : ∃j≥JJ,∃ᶠ t:ℕ in atTop,
      δ*((lengthAt t:ℝ)*rowWidth j (lengthAt t))≤cleanMass A d K L (lengthAt t) (rowWidth j (lengthAt t)) := by
    obtain ⟨j,jJ,freq⟩:=counts JJ
    refine ⟨j,jJ,freq.mono (fun t good=>?_)⟩
    dsimp only at good
    rcases good with one|⟨p,hp,q,hq,ne,more⟩
    · exact one.trans (clean_ge_first _ _ _ _ _ _)
    · rw [clean_mass]
      exact more.trans (add_le_add_right (intersection_le_multiple hp hq ne) _)
  refine ⟨L,surplus_of_mass (cleanMass A d K L) rows
    ⟨I,fun j hj=>length_grows.eventually (fit j hj)⟩ (sharp_transfer l2 cn row)
      (by omega:2≤K) kl inT inAux δp ?_⟩
  rw [div_div,div_lt_iff₀ (mul_pos logp lp)]
  linarith [show δ*((L:ℝ)*Real.log L)=2*(δ/2*(Real.log L*L)) by ring]

end
end Sun28.CommonRows
#print axioms Sun28.CommonRows.positive_surplus