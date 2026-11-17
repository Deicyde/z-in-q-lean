import ThetaSectionUniqueness
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealZeroSchemeIdealInvModuleSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.ZeroSchemeIdealCompEq
import Nyll.AlgebraicCurves.Geometry.Sheaves.Sections.SectionVanishingClosedSubscheme
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierInvertibility

/-! Effective Cartier divisors in a complete linear system of dimension zero. -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace ZInQBlueprint.ThetaLinearSystem
noncomputable section
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The canonical Cartier section is nonzero on every nonempty scheme. -/
theorem canonical_ne_zero [Nonempty X] {I : X.IdealSheafData} (hI : I.IsInvertible) :
    I.invModuleSection ≠ 0 := by
  intro h
  have hi : I = ⊥ := hI.zeroSchemeIdeal_invModuleSection.symm.trans
    ((hI.isInvertible_invModule.zeroSchemeIdeal_eq_bot_iff I.invModuleSection).mpr h)
  let x : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨U,f,hx,g,hg,hgen⟩ := hI x
  have : Nonempty (X.affineBasicOpen f).1 := ⟨⟨x,hx⟩⟩
  have hzero : I.ideal (X.affineBasicOpen f) = ⊥ := by rw [hi]; rfl
  exact (nonZeroDivisors.ne_zero hg) (Ideal.span_singleton_eq_bot.mp (hgen.symm.trans hzero))

private theorem ideal_eq_if_empty [IsEmpty X] (I J : X.IdealSheafData) : I = J := by
  apply Scheme.IdealSheafData.ext
  funext U
  have hU : U.1 = ⊥ := by
    ext x
    exact isEmptyElim x
  have : Subsingleton Γ(X,U.1) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hU)
  exact Subsingleton.elim _ _

/-- Two linearly equivalent effective Cartier divisors with a one-dimensional
space of global sections are equal as closed subschemes, with all multiplicities. -/
theorem effective_eq_of_linearly_equivalent (c : X ⟶ Spec (.of k))
    {I J : X.IdealSheafData} (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (h0 : rankH0 c J.invModule = 1) (equiv : Nonempty (I.invModule ≅ J.invModule)) : I = J := by
  rcases isEmpty_or_nonempty X with h | h
  · exact ideal_eq_if_empty I J
  obtain ⟨e⟩ := equiv
  have hi := hI.isInvertible
  have hj := hJ.isInvertible
  have hs : I.invModuleSection ≫ e.hom ≠ 0 := by
    intro h
    apply canonical_ne_zero hi
    exact (cancel_mono e.hom).1 (by simpa only [Limits.zero_comp] using h)
  have h := zeroScheme_eq c J.invModule hj.isInvertible_invModule h0
    (I.invModuleSection ≫ e.hom) J.invModuleSection hs (canonical_ne_zero hj)
  rwa [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso, hi.zeroSchemeIdeal_invModuleSection,
    hj.zeroSchemeIdeal_invModuleSection] at h

end
end ZInQBlueprint.ThetaLinearSystem
#print axioms ZInQBlueprint.ThetaLinearSystem.canonical_ne_zero
#print axioms ZInQBlueprint.ThetaLinearSystem.effective_eq_of_linearly_equivalent
