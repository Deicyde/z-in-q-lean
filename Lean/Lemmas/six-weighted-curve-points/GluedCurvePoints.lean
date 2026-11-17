import SexticAffinePoints

/-! The two affine pullback squares identify every section of a glued double cover. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] (f g : K[X]) (h : SexticOverlap K f g)

def chartSection (i : Bool) (p : AffineCoords K (if i then g else f)) :
    Sections K (gluedOver K f g h) :=
  affineSection K _ p ≫ chartInclusion K f g h i

theorem chartSection_injective (i : Bool) : Function.Injective (chartSection f g h i) := by
  intro p q e
  apply (affineSection_bijective K _).1
  apply Over.OverMorphism.ext
  apply (cancel_mono (chartInclusion K f g h i).left).mp
  exact congrArg (fun q : Sections K (gluedOver K f g h) => q.left) e

theorem chartSection_line (i : Bool) (p : AffineCoords K (if i then g else f)) :
    (chartSection f g h i p).left ≫ toLine K f g h = point K (RingHom.id K) p.1.1 i := by
  have s := (chart_pullback K f g h (some i)).w
  change ordinateProjection K _ ≫ inclusion K i = (chartInclusion K f g h i).left ≫ toLine K f g h at s
  change ((affineSection K _ p).left ≫ _) ≫ _ = _
  rw [Category.assoc, ← s, ← Category.assoc, affine_fst]
  rfl

theorem chartSection_above (m : Sections K (gluedOver K f g h)) (i : Bool) (x : K)
    (he : point K (RingHom.id K) x i = m.left ≫ toLine K f g h) :
    ∃ p : AffineCoords K (if i then g else f), p.1.1 = x ∧ chartSection f g h i p = m := by
  let sq := chart_pullback K f g h (some i)
  let v := Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id K) x))
  let q := sq.lift v m.left he
  have hq : q ≫ (chartInclusion K f g h i).left = m.left := sq.lift_snd ..
  let n : Sections K (SpecOver (R := K) (Cover (if i then g else f))) :=
    Over.homMk q (by
      rw [← (chartInclusion K f g h i).w, ← Category.assoc,hq]
      exact m.w)
  obtain ⟨p,hp⟩ := (affineSection_bijective K _).2 n
  have eq : chartSection f g h i p = m := by
    apply Over.OverMorphism.ext
    change (affineSection K _ p).left ≫ _ = m.left
    rw [hp]
    exact hq
  refine ⟨p,point_injective K (RingHom.id K) i ?_,eq⟩
  change point K (RingHom.id K) p.1.1 i = point K (RingHom.id K) x i
  rw [←chartSection_line f g h i p,eq,he]

abbrev GluedCoords := AffineCoords K f ⊕ {y : K // y^2 = aeval (0:K) g}

def infinityCoord (w : {y : K // y^2 = aeval (0:K) g}) : AffineCoords K g := ⟨(0,w.1),w.2⟩

def coordsSection : GluedCoords f g → Sections K (gluedOver K f g h)
  | .inl p => chartSection f g h false p
  | .inr w => chartSection f g h true (infinityCoord g w)

theorem coordsSection_injective : Function.Injective (coordsSection f g h) := by
  rintro (p | p) (q | q) e
  · exact congrArg Sum.inl (chartSection_injective f g h false e)
  · have eu := congrArg (fun q : Sections K (gluedOver K f g h) => q.left ≫ toLine K f g h) e
    change (chartSection f g h false p).left ≫ _ = (chartSection f g h true (infinityCoord g q)).left ≫ _ at eu
    rw [chartSection_line,chartSection_line] at eu
    simpa [infinityCoord] using cross_product K (RingHom.id K) eu
  · have eu := congrArg (fun q : Sections K (gluedOver K f g h) => q.left ≫ toLine K f g h) e.symm
    change (chartSection f g h false q).left ≫ _ = (chartSection f g h true (infinityCoord g p)).left ≫ _ at eu
    rw [chartSection_line,chartSection_line] at eu
    simpa [infinityCoord] using cross_product K (RingHom.id K) eu
  · have eq := chartSection_injective f g h true e
    exact congrArg Sum.inr (Subtype.ext (congrArg (fun q => q.1.2) eq))

theorem coordsSection_surjective : Function.Surjective (coordsSection f g h) := by
  intro m
  let v := m.left ≫ toLine K f g h
  have hv : v ≫ lineStructure K = Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
    change (m.left ≫ _) ≫ _ = Spec.map (𝟙 (CommRingCat.of K))
    rw [Category.assoc,curve_structure,Spec.map_id]
    exact m.w
  have finite (x:K) (he : point K (RingHom.id K) x false = v) : ∃ a, coordsSection f g h a = m := by
    obtain ⟨p,_,hp⟩ := chartSection_above f g h m false x he
    exact ⟨.inl p,hp⟩
  obtain ⟨i,x,hx⟩ := exists_coordinates K (RingHom.id K) v hv
  cases i with
  | false => exact finite x hx
  | true =>
    by_cases h0 : x = 0
    · subst x
      obtain ⟨⟨⟨xp,yp⟩,hp⟩,hx0,hm⟩ := chartSection_above f g h m true 0 hx
      change xp=0 at hx0
      subst xp
      exact ⟨.inr ⟨yp,hp⟩,hm⟩
    · apply finite x⁻¹
      exact (point_invert K (RingHom.id K) (Units.mk0 x h0)⁻¹).trans (by simpa using hx)

def gluedPointEquiv : GluedCoords f g ≃ Sections K (gluedOver K f g h) :=
  Equiv.ofBijective (coordsSection f g h) ⟨coordsSection_injective f g h,coordsSection_surjective f g h⟩
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.chartSection_line
#print axioms ZInQBlueprint.WeightedCurvePoints.chartSection_above
#print axioms ZInQBlueprint.WeightedCurvePoints.gluedPointEquiv
