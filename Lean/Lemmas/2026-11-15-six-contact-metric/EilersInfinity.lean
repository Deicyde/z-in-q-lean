import EilersCharacteristics

/-! The scope of the even-pair notation in Eilers (4.4), with base point at infinity. -/
namespace ZInQBlueprint.SixMetric
open OriginalTheta ZInQ.LeafPush2

def singleChar (i : Fin 6) : Char2 := halfPeriod i - riemannConstant

theorem singleton_indices : (fun i => number (singleChar i)) =
    ![(10 : Fin 16),11,7,5,13,14] := by
  funext i
  fin_cases i <;> rfl

theorem singleton_odd (i : Fin 6) : dotParity (singleChar i) = 1 := by
  fin_cases i <;> decide

/-- Pairing a finite point with the sixth point repeats an odd singleton. -/
theorem pair_with_infinity (i : Fin 5) :
    halfPeriod i.castSucc + halfPeriod (Fin.last 5) - riemannConstant = singleChar i.castSucc ∧
    dotParity (halfPeriod i.castSucc + halfPeriod (Fin.last 5) - riemannConstant) = 1 := by
  have e : halfPeriod (Fin.last 5) = 0 := by decide
  rw [e, add_zero]
  exact ⟨rfl, singleton_odd _⟩

theorem theta_pair_with_infinity (Ω : Matrix (Fin 2) (Fin 2) ℂ) (h : IsSiegel Ω) (i : Fin 5) :
    thetaConst Ω (halfPeriod i.castSucc + halfPeriod (Fin.last 5) - riemannConstant) = 0 :=
  thetaConst_odd Ω h _ (pair_with_infinity i).2

end ZInQBlueprint.SixMetric

#print axioms ZInQBlueprint.SixMetric.singleton_indices
#print axioms ZInQBlueprint.SixMetric.singleton_odd
#print axioms ZInQBlueprint.SixMetric.pair_with_infinity
#print axioms ZInQBlueprint.SixMetric.theta_pair_with_infinity
