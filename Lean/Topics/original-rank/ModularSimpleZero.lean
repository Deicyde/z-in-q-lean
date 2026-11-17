import PrintedTwists
import ZInQKernel.Contrib.OneProof.TopChain

namespace ZInQBlueprint.OriginalRank

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ ZInQ.Literature ZInQ.RouteK.Rank5b
open ZInQ.GZDecomp

/-- Gross–Zagier, Chapter I, Theorem 7.3(1), in the newform formulation of
modularity. The arithmetic and Fourier coefficients agree at every positive
index. The continuation and its derivative refer to that same newform. -/
def ModularSimpleZero : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2),
    f.χ = 1 → (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ F : ℂ → ℂ, IsEntireCont (coeff f) 2 F → F 1 = 0 → deriv F 1 ≠ 0 →
      ∃ P : E.toAffine.Point, ¬IsOfFinAddOrder P

/-- For the twists used by the polynomial, the arithmetic L-function is the
L-function of an actual weight-two newform. A simple central zero therefore
meets every premise in the published positive-rank criterion. -/
theorem selected_rank_of_modular_simple_zero (rank : ModularSimpleZero) :
    SelectedTwists.SelectedGrossZagier := by
  intro d hd hsq _ F hF hder
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  letI : (shortCurve (-(d : ℚ) ^ 2)).IsElliptic :=
    shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 hd0))
  obtain ⟨N, hN, f, hχ, hf⟩ := modular_cd ZInQ.GZTheta.Frontier.heckeThetaNewform
    (d := d) (by omega) hsq
  exact rank _ N f hχ hf F (isEntireCont_of_isLContinuation hf hF)
    (rootNumberVanishing_of_functionalEquation ZInQ.Contrib.functionalEquation5 d hd hsq F hF) hder

/-- The bounded polynomial theorem from the intrinsic height, the printed
genus coefficient, and the published modular simple-zero criterion. -/
theorem frozen_of_height_printed_modular_simple_zero (height : BranchHeight.CanonicalBranchBound)
    (bracket : SelectedTwists.PrintedBracketDerivative) (rank : ModularSimpleZero) :
    ZInQ.FrozenTarget :=
  SelectedTwists.frozen_of_printed_bracket height bracket (selected_rank_of_modular_simple_zero rank)

end ZInQBlueprint.OriginalRank

#print axioms ZInQBlueprint.OriginalRank.selected_rank_of_modular_simple_zero
#print axioms ZInQBlueprint.OriginalRank.frozen_of_height_printed_modular_simple_zero
