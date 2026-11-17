import RemainingProjection

namespace Sun28.ConicRemaining
open Sun28.ScalarRankZero WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open Sun28.ScalarDepth Height ZInQ ZInQ.Mult Sun28.ConicArithmetic Sun28.ScalarHeight Sun28.Ordinary
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 2200

abbrev ShortPoints := (curve 735 134288).toAffine.Point
def ShortRankZero : Prop := Module.rank ℤ ShortPoints=0

/-- At the good prime 3 the reduction has four elements. -/
private def ResidueFour : ResiduePoints 3 735 134288 ≃ Fin 4 :=
  Fintype.equivFinOfCardEq (by decide)

private theorem nonsquare : ¬IsSquare (134288:ℚ) := by
  intro sq
  obtain ⟨k,h⟩:=(Rat.isSquare_intCast_iff (z:=134288)).mp (by exact_mod_cast sq)
  have test:∀ r:ZMod 3, r^2≠(134288:ZMod 3):=by decide
  apply test (k:ZMod 3)
  simpa [pow_two] using congrArg (Int.castRingHom (ZMod 3)) h.symm

private theorem ns {x y:ℚ} (yn:y≠0) (eq:y^2=x*(x^2+735*x+134288)):
    (curve 735 134288).toAffine.Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff',WeierstrassCurve.Affine.equation_iff]
  constructor
  · simp [curve] at *;linear_combination eq
  · right;simp [curve,yn]

/-- Rank zero and the existing good-reduction interface suffice. An alleged positive point
gives five distinct points using the reciprocal abscissa 134288/x. -/
theorem short_bound_of_rank (rank:ShortRankZero) (red:OddGoodReduction) : ShortCurveBound := by
  intro X Y xp eq
  have torsion (P:ShortPoints) : IsOfFinAddOrder P:=
    isOfFinAddOrder_iff_zsmul_eq_zero.mpr (rank_eq_zero_iff.mp rank P)
  obtain ⟨inj⟩:=red 735 134288 3 (by decide) (by decide) (by decide)
  let incl : ShortPoints ↪ {P:ShortPoints // IsOfFinAddOrder P} :=
    ⟨fun P=>⟨P,torsion P⟩,fun _ _ h=>congrArg Subtype.val h⟩
  let into:=incl.trans (inj.trans ResidueFour.toEmbedding)
  have yn:Y≠0:=by
    intro e
    have p:0<X*(X^2+735*X+134288):=by positivity
    rw[e] at eq
    have eq0:X*(X^2+735*X+134288)=0:=by simpa only [zero_pow (by decide:2≠0)] using eq.symm
    exact p.ne' eq0
  let X':ℚ:=134288/X
  let Y':ℚ:=134288*Y/X^2
  have xn:X≠0:=xp.ne'
  have y'n:Y'≠0:=by dsimp[Y'];exact div_ne_zero (mul_ne_zero (by norm_num) yn) (pow_ne_zero 2 xn)
  have e':Y'^2=X'*(X'^2+735*X'+134288):=by dsimp[X',Y'];field_simp[xn];linear_combination eq
  have ne:X≠X':=by
    intro h;apply nonsquare;refine ⟨X,?_⟩
    have hx: X*X=134288:=(eq_div_iff xn).mp h
    exact hx.symm
  let P (x y:ℚ) (hn:y≠0) (w:y^2=x*(x^2+735*x+134288)) : ShortPoints := .some x y (ns hn w)
  let f : Fin 5 → ShortPoints := ![0,P X Y yn eq,P X (-Y) (neg_ne_zero.mpr yn) (by simpa only [neg_sq] using eq),
      P X' Y' y'n e',P X' (-Y') (neg_ne_zero.mpr y'n) (by simpa only [neg_sq] using e')]
  have ny:Y≠ -Y:=by intro hh;apply yn;linarith
  have ny':Y'≠ -Y':=by intro hh;apply y'n;linarith
  have oneone:Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f,P]
  have cards:=Fintype.card_le_of_injective (into ∘ f) (into.injective.comp oneone)
  norm_num at cards

theorem no_positive_of_rank (sel:PositiveSelmerSelection) (rank:ShortRankZero)
    (red:OddGoodReduction) (x:ℚ) : ¬Sun28.ConicCovers.positiveParameter x :=
  no_positive_parameter sel (short_bound_of_rank rank red) x

theorem scalar_of_short_rank (descent:TwoIsogenyRank) (reduction:OddGoodReduction)
    (sel:PositiveSelmerSelection) (rank:ShortRankZero) (est:NegativeExceptionalScalarBound) : ScalarBound :=
  scalar_of_negative_exceptions descent reduction sel (short_bound_of_rank rank reduction) est

end
end Sun28.ConicRemaining
#print axioms Sun28.ConicRemaining.short_bound_of_rank
#print axioms Sun28.ConicRemaining.no_positive_of_rank
#print axioms Sun28.ConicRemaining.scalar_of_short_rank
