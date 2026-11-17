import SixCanonicalPeriods

/-! Forget the real marking on coarse classes, extend scalars, and compare
the two geometric points of the ordinary quotient over the complex numbers. -/
open CategoryTheory AlgebraicGeometry Polynomial
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift NormalDescent AbelianModel BinaryCover
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Isomorphism classes of commutative group schemes on a field. -/
def groupIsoSetoid (K : Type) [Field K] : Setoid (GroupScheme K) where
  r A B := Nonempty (A ≅ B)
  iseqv := ⟨fun A => ⟨Iso.refl A⟩, fun ⟨f⟩ => ⟨f.symm⟩,
    fun ⟨f⟩ ⟨g⟩ => ⟨f ≪≫ g⟩⟩

abbrev GroupIsoClass (K : Type) [Field K] := Quotient (groupIsoSetoid K)

def groupClass {K : Type} [Field K] (A : GroupScheme K) : GroupIsoClass K :=
  Quotient.mk _ A

theorem groupClass_eq {K : Type} [Field K] {A B : GroupScheme K} :
    groupClass A = groupClass B ↔ Nonempty (A ≅ B) :=
  Quotient.eq

/-- Forgetting the line and the marked generator, followed by extension to
ℂ, is defined on the geometric coarse equivalence classes themselves. -/
def forgetComplex (ι : Qbar →+* ℂ) : ModuliClass → GroupIsoClass ℂ :=
  Quotient.map (fun a : RealLabel => (baseChange ι).obj a.surface) (by
    intro a b equivalent
    obtain ⟨f, _⟩ := equivalent
    exact ⟨(baseChange ι).mapIso f⟩)

theorem forgetComplex_label (ι : Qbar →+* ℂ) (a : RealLabel) :
    forgetComplex ι (moduliClass a) = groupClass ((baseChange ι).obj a.surface) := rfl

/-- For abelian representatives this comparison detects precisely unmarked
isomorphism already over the algebraic closure. -/
theorem forgetComplex_eq_iff {ι : Qbar →+* ℂ} (hom : HomBaseChange ι)
    (a b : RealLabel) (aa : IsAbelianScheme a.surface) (bb : IsAbelianScheme b.surface) :
    forgetComplex ι (moduliClass a) = forgetComplex ι (moduliClass b) ↔
      Nonempty (a.surface ≅ b.surface) := by
  rw [forgetComplex_label, forgetComplex_label, groupClass_eq]
  exact ⟨fun ⟨f⟩ => ⟨descendIso hom aa bb f⟩, fun ⟨f⟩ => ⟨(baseChange ι).mapIso f⟩⟩

abbrev complexDomain := SpecOver (R := ℚ) ℂ

def extendPoint (ι : Qbar →+* ℂ) : complexDomain ⟶ geometricDomain := specHom ι.toRatAlgHom

def complexLinePoint (t : ℂ) : complexDomain ⟶ Line := specHom (aeval t)

theorem extend_linePoint (ι : Qbar →+* ℂ) (t : Qbar) :
    extendPoint ι ≫ linePoint t = complexLinePoint (ι t) := by
  rw [extendPoint, linePoint, spec_comp, complexLinePoint]
  congr 1
  ext
  simp

/-- The degree-two forgetful map to the full Atkin--Lehner quotient in the
coordinate t = 3z/y and x = 4. Here j = y²/9. -/
theorem j_quotient (p : ConicPoint) :
    p.y^2 * (p.quotientCoordinate^2+27) = -144 := by
  change p.y^2 * ((3*p.z/p.y)^2+27) = -144
  field_simp [p.y_ne]
  linear_combination 9*p.onCurve

/-- The homogeneous modular conic coordinates determine the same complex
point on the real-labelled quotient for every upper-half-plane lift. -/
theorem quotient_of_lift {ι : Qbar →+* ℂ} {A Y Z : ℂ} {p : ConicPoint}
    (h : LiesAbove ι A Y Z p) :
    Y ≠ 0 ∧ complexLinePoint (3*Z/Y) = extendPoint ι ≫ linePoint p.quotientCoordinate := by
  obtain ⟨hA,hY,hZ⟩ := h
  have hy : ι p.y ≠ 0 := (map_ne_zero_iff ι ι.injective).mpr p.y_ne
  have hY' : Y ≠ 0 := by
    intro zero
    exact (mul_ne_zero hA hy) (by rw [←hY,zero,mul_zero])
  refine ⟨hY', ?_⟩
  rw [extend_linePoint]
  congr 1
  change 3*Z/Y = ι (3*p.z/p.y)
  rw [map_div₀,map_mul,map_ofNat]
  apply (div_eq_div_iff hY' hy).mpr
  linear_combination 3*ι p.y*hZ/4 - 3*ι p.z*hY/4

/-- Full-order representatives on the ordinary coarse Shimura locus. The
action and principal polarization live over the algebraic closure. -/
structure OrdinarySurface where
  surface : GroupScheme Qbar
  abelian : IsAbelianScheme surface
  theta : surface.X.left.Modules
  principal : EffectivePrincipal abelian theta
  order : LevelThree.O ≃+* End surface

def OrdinarySurface.coarseClass (w : OrdinarySurface) : ModuliClass :=
  moduliClass (markedObject w.surface w.theta w.order.toRingHom)

/-- Membership in the geometric-point moduli problem of the ordinary
quotient, expressed on its affine coordinate t independently of any period. -/
def AlgebraicOrdinaryClasses {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) : Prop :=
  ∀ (t : Qbar) (j : ℚ), OutsideCM j → (j : Qbar)*(t^2+27) = -16 →
    C.read (linePoint t ≫ chart) ∈ Set.range OrdinarySurface.coarseClass

/-- Naturality of the unmarked geometric class for extension from Qbar
to ℂ. This concerns every point of the coarse moduli scheme. -/
def ForgetfulNaturality {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M) (ι : Qbar →+* ℂ)
    (readC : (complexDomain ⟶ M) → GroupIsoClass ℂ) : Prop :=
  ∀ x : geometricDomain ⟶ M, readC (extendPoint ι ≫ x) = forgetComplex ι (C.read x)

/-- Geometric-point description on the complex affine chart in
Baba--Granath, Theorem 2.1 and Corollary 3.11. -/
def AnalyticQuotient {M : Over (Spec (.of ℚ))} (chart : Line ⟶ M)
    (readC : (complexDomain ⟶ M) → GroupIsoClass ℂ)
    (Y Z : UpperHalfPlane → ℂ) (surface : UpperHalfPlane → GroupScheme ℂ) : Prop :=
  ∀ τ, Y τ ≠ 0 → readC (complexLinePoint (3*Z τ/Y τ) ≫ chart) = groupClass (surface τ)

def OrdinarySurface.toRepresentative {M : Over (Spec (.of ℚ))} {C : CoarseInterpretation M}
    {chart : Line ⟶ M} {ι : Qbar →+* ℂ} (hom : HomBaseChange ι) {p : ConicPoint}
    (w : OrdinarySurface) (hw : C.read (linePoint p.quotientCoordinate ≫ chart) = w.coarseClass) :
    PeriodRepresentative C chart ι hom p where
  surface := w.surface
  abelian := w.abelian
  theta := w.theta
  principal := w.principal
  complexOrder := w.order.trans (endBaseEquiv hom w.surface w.abelian)
  represents := by
    have h : descendedOrder hom w.surface w.abelian
        (w.order.trans (endBaseEquiv hom w.surface w.abelian)) = w.order := by
      apply RingEquiv.ext
      intro r
      exact (endBaseEquiv hom w.surface w.abelian).symm_apply_apply _
    rw [h]
    exact hw

/-- An ordinary geometric representative selected before choosing any
complex lift works at every lift of the specified conic point. -/
theorem ordinary_representative {M : Over (Spec (.of ℚ))} {C : CoarseInterpretation M}
    {chart : Line ⟶ M} {ι : Qbar →+* ℂ} (hom : HomBaseChange ι)
    {readC : (complexDomain ⟶ M) → GroupIsoClass ℂ}
    (algebraic : AlgebraicOrdinaryClasses C chart) (natural : ForgetfulNaturality C ι readC)
    {A Y Z : UpperHalfPlane → ℂ} {surface : UpperHalfPlane → GroupScheme ℂ}
    (analytic : AnalyticQuotient chart readC Y Z surface) (j : ℚ) (ordinary : OutsideCM j)
    (p : ConicPoint) (hj : p.y^2 = 9 * (j:Qbar)) :
    ∃ w : PeriodRepresentative C chart ι hom p, ∀ τ : UpperHalfPlane,
      LiesAbove ι (A τ) (Y τ) (Z τ) p → Nonempty ((baseChange ι).obj w.surface ≅ surface τ) := by
  have jt := j_quotient p
  rw [hj] at jt
  obtain ⟨w, hw⟩ := algebraic p.quotientCoordinate j ordinary (by linear_combination jt/9)
  refine ⟨w.toRepresentative hom hw.symm, ?_⟩
  intro τ hτ
  have ⟨hy, he⟩ := quotient_of_lift hτ
  apply groupClass_eq.mp
  change forgetComplex ι w.coarseClass = groupClass (surface τ)
  rw [hw, ←natural, ←Category.assoc, ←he]
  exact analytic τ hy

end
end ZInQBlueprint.ShimuraAtlas

#print axioms ZInQBlueprint.ShimuraAtlas.forgetComplex_eq_iff
#print axioms ZInQBlueprint.ShimuraAtlas.extend_linePoint
#print axioms ZInQBlueprint.ShimuraAtlas.j_quotient
#print axioms ZInQBlueprint.ShimuraAtlas.quotient_of_lift
#print axioms ZInQBlueprint.ShimuraAtlas.ordinary_representative
