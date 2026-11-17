import SixRawPeriodCurve

/-! The Jacobian in Baba–Granath's modular-form equation is computed over
the complex numbers. Compare it to the scalar extension of the normalized
algebraic Jacobian through the signed rational curve. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open JacobianVarieties.Picard.Unpointed
namespace ZInQBlueprint.ShimuraAtlas
open BinaryCover QuaternionLift NormalDescent AbelianModel PrintedModel
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

private theorem map_modular (ι : Qbar →+* ℂ) (s k : Qbar) :
    (modularPolynomial s k).map ι = modularPolynomial (ι s) (ι k) := by
  simp [modularPolynomial, modularBinary, map_div₀, map_ofNat]

private theorem completion_eq {f g : ℂ[X]} (eq : f = g)
    (hf : f.natDegree = 6) (hg : g.natDegree = 6) :
    sexticCompletion f hf = sexticCompletion g hg := by
  cases eq
  rfl

/-- The proper curve of the normalized complex equation is a model of
the same signed rational curve for the chosen embedding and both radicals. -/
private def signedNormalizedComplex {u : ℚ} (hu : u ∉ ZInQ.contactSet) {p : ConicPoint}
    (hp : FibrePoint u p) {e l : Qbar} (he : e^2 = -6) (hl : l^2 = 2)
    (ι : Qbar →+* ℂ) (hn : ((modularPolynomial (e*p.y/3) (l*p.z)).map ι).natDegree = 6) :
    paperPullback ℂ u ≅ sexticCompletion ((modularPolynomial (e*p.y/3) (l*p.z)).map ι) hn := by
  let s := e*p.y/3
  let k := l*p.z
  let d := rad (u:=u) (p:=p) (e:=e)
  obtain ⟨hd, hs, hk, hk₀⟩ := rad_spec hu hp he hl
  have hd' : (ι d)^2 = 6 := by simpa [d, map_ofNat] using congrArg ι hd
  have hs' : argument u (ι d) = -(ι s) := by
    simpa [argument,d,s] using congrArg ι hs
  have hk' : (ι k)^2 = 9*(ι s)^2-32 := by simpa [s,k,map_ofNat] using congrArg ι hk
  have hk₀' : ι k ≠ 0 := (map_ne_zero ι).mpr hk₀
  choose v hv using IsAlgClosed.exists_pow_nat_eq (factor u (ι d)) (by decide : 0 < 2)
  choose w hw using IsAlgClosed.exists_pow_nat_eq (-4*(ι k)^6) (by decide : 0 < 2)
  let iso := (modular_completion hu hd' hs' hk' hk₀' hw).exists.choose
  exact PrintedModel.curveIso hu hd' v hv ≪≫ iso.symm ≪≫
    eqToIso (completion_eq (map_modular ι s k).symm _ hn)

/-- The raw period sextic at any lift of an off-contact parameter is an
actual smooth proper model of the signed curve over the complex numbers. -/
theorem raw_signed_curve {u : ℚ} (hu : u ∉ ZInQ.contactSet) {p : ConicPoint}
    (hp : FibrePoint u p) {e l : Qbar} (he : e^2 = -6) (hl : l^2 = 2) (ι : Qbar →+* ℂ)
    {A Y Z : ℂ} (above : LiesAbove ι A Y Z p) :
    let f := rawPolynomial A (ι e*Y) (2*ι l*Z)
    ∃ (hd : f.natDegree = 6), f.Separable ∧
      Nonempty (paperPullback ℂ u ≅ sexticCompletion f hd) := by
  obtain ⟨hn,hr,_,sr,_,uniq⟩ := raw_models hu hp he hl ι above
  exact ⟨hr,sr,⟨signedNormalizedComplex hu hp he hl ι hn ≪≫ uniq.exists.choose⟩⟩

/-- Composition of the two base changes on schemes. This applies to every
embedding of the algebraic closure, independently of its action on radicals. -/
private def rationalPullback (ι : Qbar →+* ℂ) (u : ℚ) :
    paperPullback ℂ u ≅ (Over.pullback (Spec.map (CommRingCat.ofHom ι))).obj (paperPullback Qbar u) := by
  let f := Spec.map (CommRingCat.ofHom ι)
  have h : f ≫ scalarMap ℚ Qbar = scalarMap ℚ ℂ := by
    simp only [f,scalarMap,← Spec.map_comp]
    congr 1
    ext q
    exact map_ratCast ι q
  exact ((eqToIso (congrArg (fun g => Over.pullback g) h.symm)) ≪≫
    Over.pullbackComp f (scalarMap ℚ Qbar)).app (paperModel ℚ u)

/-- The Jacobian of the literal complex sextic agrees, as a group scheme,
with the scalar extension of the algebraic modular Jacobian. -/
theorem raw_jacobian {u : ℚ} (hu : u ∉ ZInQ.contactSet) {p : ConicPoint}
    (hp : FibrePoint u p) {e l : Qbar} (he : e^2 = -6) (hl : l^2 = 2) (ι : Qbar →+* ℂ)
    {A Y Z : ℂ} (above : LiesAbove ι A Y Z p) :
    let f := rawPolynomial A (ι e*Y) (2*ι l*Z)
    ∃ (hd : f.natDegree = 6), f.Separable ∧
      ∃ (_ : IsProper (sexticCompletion f hd).hom)
        (_ : SmoothOfRelativeDimension 1 (sexticCompletion f hd).hom)
        (_ : GeometricallyIrreducible (sexticCompletion f hd).hom),
        Nonempty ((baseChange ι).obj (modularJacobian hu hp he hl) ≅
          groupScheme ℂ (sexticCompletion f hd).hom) := by
  dsimp only
  let f := rawPolynomial A (ι e*Y) (2*ι l*Z)
  obtain ⟨hd,hs,⟨a⟩⟩ := raw_signed_curve hu hp he hl ι above
  let D := sexticCompletion f hd
  obtain ⟨hI,hP,hS,hD,_⟩ := sexticCompletion_geometry hd hs
  let : AlgebraicGeometry.IsIntegral D.left := hI
  let : IsProper D.hom := hP
  let : Smooth D.hom := hS
  let : SmoothOfRelativeDimension 1 D.hom := SixJacobian.relative_dimension_one _ hD
  let : IsIso a.inv.left := inferInstanceAs (IsIso (((Over.forget _).mapIso a).inv))
  let : GeometricallyIntegral (paperModel ℚ u).hom := geometricallyIntegral_paperModel hu
  have hG : GeometricallyIrreducible (paperPullback ℂ u).hom :=
    inferInstanceAs (GeometricallyIrreducible (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ ℂ)))
  have sq : IsPullback a.inv.left D.hom (paperPullback ℂ u).hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact a.inv.w⟩
  let : GeometricallyIrreducible D.hom := MorphismProperty.of_isPullback (P := @GeometricallyIrreducible) sq hG
  let : Algebra Qbar ℂ := ι.toAlgebra
  let iso := (Over.pullback (Spec.map (CommRingCat.ofHom ι))).mapIso (signedToModular hu hp he hl).symm ≪≫
    (rationalPullback ι u).symm ≪≫ a
  exact ⟨hd,hs,hP,inferInstanceAs (SmoothOfRelativeDimension 1 D.hom),
    inferInstanceAs (GeometricallyIrreducible D.hom),
    ⟨IntegralPicard.unpointed_baseChangeIso (modularCurve hu hp he hl) D iso⟩⟩

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.raw_signed_curve
#print axioms ZInQBlueprint.ShimuraAtlas.raw_jacobian
