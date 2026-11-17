import ConeRecords

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
namespace Sun28.ConeFibres
open Finset Sun28.MixedSieve
open scoped Classical
noncomputable section

variable {p : ℕ} [Fact p.Prime]

def chi (p : ℕ) [Fact p.Prime] : ℤ := legendreSym p (-1)

def circleCount (t : ZMod p) : ℤ := Fintype.card (Circle p t)

theorem circle_count (odd : p ≠ 2) (t : ZMod p) :
    circleCount t = ((p:ℤ)-chi p) + if t=0 then (p:ℤ)*chi p else 0 := by
  let h : ℤ := (p:ℤ)-chi p
  have sumNat := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun x : ZMod p × ZMod p => x.1^2+x.2^2))
  have sumZ : (∑ t : ZMod p, circleCount t) = (p:ℤ)^2 := by
    change (∑ t : ZMod p, (Fintype.card (Circle p t):ℤ)) = _
    have sumN : (∑ t : ZMod p, Fintype.card (Circle p t)) = p^2 := by
      simpa only [Fintype.card_sigma,Fintype.card_prod,ZMod.card,MixedSieve.Circle,pow_two] using sumNat
    exact_mod_cast sumN
  have f (z : ZMod p) : circleCount z = h + if z=0 then circleCount (0:ZMod p)-h else 0 := by
    by_cases hz : z=0
    · simp [hz]
    · simpa [hz,h,chi,circleCount] using circle_card odd hz
  rw [sum_congr rfl (fun t _ => f t)] at sumZ
  simp [sum_add_distrib,ZMod.card] at sumZ
  by_cases ht : t=0
  · subst t
    simp only [ite_true]
    dsimp [h,chi] at sumZ ⊢
    linear_combination sumZ
  · simpa [ht,chi,circleCount] using circle_card odd ht

/-- Correlation of two norm fibres restricted to any set containing their two centres. -/
theorem restricted_moment (odd : p ≠ 2) (S : Finset (ZMod p)) (c : ZMod p)
    (zS : 0∈S) (cS : c∈S) :
    ∑ t ∈ S, circleCount t * circleCount (t-c) =
      (S.card:ℤ)*((p:ℤ)-chi p)^2 + 2*((p:ℤ)-chi p)*((p:ℤ)*chi p)
        + if c=0 then ((p:ℤ)*chi p)^2 else 0 := by
  let a : ℤ := (p:ℤ) - chi p
  let b : ℤ := (p:ℤ) * chi p
  have each (t : ZMod p) : circleCount t * circleCount (t-c) =
      a^2+(if t=0 then a*b else 0)+(if t=c then a*b else 0)+
        (if c=0 then (if t=0 then b^2 else 0) else 0) := by
    rw [circle_count odd, circle_count odd]
    change (a + _) * (a + _) = _
    by_cases hc : c=0
    · subst c
      by_cases ht : t=0 <;> simp [ht,a,b] <;> ring
    · by_cases ht : t=0
      · subst t
        simp [hc,Ne.symm hc,a,b]
        <;> ring
      · by_cases he : t=c <;> simp [hc,ht,he,sub_eq_zero,a,b] <;> ring
  simp_rw [each]
  by_cases hc : c=0 <;>
    simp [sum_add_distrib,hc,zS,cS,a,b] <;> ring

end
end Sun28.ConeFibres
#print axioms Sun28.ConeFibres.circle_count
#print axioms Sun28.ConeFibres.restricted_moment
