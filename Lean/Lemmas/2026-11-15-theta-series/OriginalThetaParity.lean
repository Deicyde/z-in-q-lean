import OriginalThetaSeries
import ThetaParity

namespace ZInQBlueprint.OriginalTheta
open ThetaPeriod ThetaQuotient ZInQ.LeafPush2

/-- The ordinary dot-product parity of an ordered pair of binary characteristics. -/
def dotParity (m : Char2) : Fin 2 :=
  m.1 0 * m.2 0 + m.1 1 * m.2 1

theorem odd_iff (j : Fin 16) :
    dotParity (characteristic j)=1 ↔ ¬∃ k, evenIndices k=j := by
  revert j
  decide

/-- Odd constants vanish at every Siegel matrix in the actual PR114 convention. -/
theorem thetaConst_odd (Ω : Matrix (Fin 2) (Fin 2) ℂ) (h : IsSiegel Ω)
    (m : Char2) (hm : dotParity m=1) : thetaConst Ω m=0 := by
  obtain ⟨j,rfl⟩ := characteristicEquiv.surjective m
  change thetaConst Ω (characteristic j)=0
  have ho := (odd_iff j).mp hm
  rw [←omega_periodOf Ω h,thetaConst_eq]
  exact thetaNull_odd _ _ ho

end ZInQBlueprint.OriginalTheta
#print axioms ZInQBlueprint.OriginalTheta.odd_iff
#print axioms ZInQBlueprint.OriginalTheta.thetaConst_odd
