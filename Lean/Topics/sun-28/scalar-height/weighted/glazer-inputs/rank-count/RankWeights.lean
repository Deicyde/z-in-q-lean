import TwoEllipticMaps

/-! Rank contributions of the two elliptic quotients at each prime of a twist. -/
namespace ZInQBlueprint.RankCount
open Finset Sun28.FiveDescent ZInQBlueprint.TwoEllipticMaps
noncomputable section

def core : Finset ℕ := {2,3,5,7}
def firstRamified (d e : ℤ) := (parameterPrimes d e).filter fun p=>p∈e.natAbs.primeFactors
def secondRamified (d e : ℤ) := (parameterPrimes d e).filter fun p=>
  ¬(p∈d.natAbs.primeFactors ↔ p∈e.natAbs.primeFactors)
def localCost (d e : ℤ) (p : ℕ) : ℕ :=
  (if p∈e.natAbs.primeFactors then 2 else 0)+
  (if p∈d.natAbs.primeFactors ↔ p∈e.natAbs.primeFactors then 0 else 2)

theorem sum_local (d e : ℤ) :
    (∑ p∈parameterPrimes d e,localCost d e p)=
      2*(firstRamified d e).card+2*(secondRamified d e).card := by
  classical
  simp only [localCost,sum_add_distrib]
  have one : (∑ p∈parameterPrimes d e, if p∈e.natAbs.primeFactors then 2 else 0) =
      2*(firstRamified d e).card := by
    rw [←sum_filter];simp [firstRamified,mul_comm]
  have two : (∑ p∈parameterPrimes d e,
      if ¬(p∈d.natAbs.primeFactors ↔ p∈e.natAbs.primeFactors) then 2 else 0)=
      2*(secondRamified d e).card := by rw [←sum_filter];simp [secondRamified,mul_comm]
  simpa only [ite_not] using congrArg₂ (·+·) one two

def rank (j : Bool) (c : ℚ) : ℕ := Module.finrank ℤ (model j c).toAffine.Point

/-- Complete rational 2-descent (Silverman, AEC X.1.4), specialized to the two
split cubics. Each term retains just four fixed primes and the ramified twist primes. -/
def DescentRankBounds : Prop := ∀ d e : ℤ, Squarefree d → Squarefree e →
  rank false (e:ℚ)≤2*(core∪firstRamified d e).card ∧
  rank true ((d:ℚ)*e)≤2*(core∪secondRamified d e).card

theorem total_rank (descent : DescentRankBounds) {d e : ℤ} (sd : Squarefree d) (se : Squarefree e) :
    rank false (e:ℚ) + rank true ((d:ℚ)*e) ≤ 16+∑ p∈parameterPrimes d e,localCost d e p := by
  obtain ⟨a,b⟩:=descent d e sd se
  have h₁:=Finset.card_union_le core (firstRamified d e)
  have h₂:=Finset.card_union_le core (secondRamified d e)
  have n:core.card=4:=by decide
  rw [sum_local];omega

/-- Silverman's 1993 Theorem 1 on the fixed genus-two curve, specialized through
its isogeny over Q to the product of the two displayed elliptic curves. -/
def FixedCurveCount (γ : ℝ) : Prop :=
  ∀ d e : ℤ, Squarefree d → Squarefree e → ∀ Y : Finset (ℚ×ℚ),
    (∀ q∈Y,q.1≠0 ∧ q.2≠0 ∧ (e:ℚ)*q.2^2=sextic d q.1) →
      (Y.card:ℝ)≤γ*(7:ℝ)^(rank false (e:ℚ)+rank true ((d:ℚ)*e))

end
end ZInQBlueprint.RankCount
#print axioms ZInQBlueprint.RankCount.sum_local
#print axioms ZInQBlueprint.RankCount.total_rank
