import FiniteDoubleCover
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.PointsPi

/-! Ring-valued points on the projective line in its two coordinate charts. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial LaurentPolynomial
namespace ZInQBlueprint.BinaryCover
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type) [CommRing R]

abbrev inclusion (i : Bool) : Spec (.of R[X]) ⟶ projectiveLine R :=
  WidePushout.ι (lineArrow R) i

theorem inclusion_structure (i : Bool) :
    inclusion R i ≫ lineStructure R = scalarMap R R[X] :=
  WidePushout.ι_desc ..

/-- A point with affine coordinate x over the ring map b. -/
def point {S : Type} [CommRing S] (b : R →+* S) (x : S) (i : Bool) :
    Spec (.of S) ⟶ projectiveLine R :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom b x)) ≫ inclusion R i

theorem point_structure {S : Type} [CommRing S] (b : R →+* S) (x : S) (i : Bool) :
    point R b x i ≫ lineStructure R = Spec.map (CommRingCat.ofHom b) := by
  rw [point, Category.assoc, inclusion_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact Polynomial.eval₂_C ..

theorem point_map {S T : Type} [CommRing S] [CommRing T] (j : S →+* T) (b : R →+* S) (x : S) (i : Bool) :
    Spec.map (CommRingCat.ofHom j) ≫ point R b x i = point R (j.comp b) (j x) i := by
  rw [point, point, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro a; change j (Polynomial.eval₂ b x (Polynomial.C a)) = Polynomial.eval₂ _ _ (Polynomial.C a)
    simp
  · change j (Polynomial.eval₂ b x Polynomial.X) = Polynomial.eval₂ _ _ Polynomial.X
    simp

theorem point_invert {S : Type} [CommRing S] (b : R →+* S) (x : Sˣ) :
    point R b (x : S) false = point R b (↑x⁻¹ : S) true := by
  let e := Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ b x))
  have left : e ≫ lineArrow R false = Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom b x)) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (LaurentPolynomial.eval₂_toLaurent b x))
  have right : e ≫ lineArrow R true = Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom b (↑x⁻¹ : S))) := by
    change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) = Spec.map _
    rw [← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      change LaurentPolynomial.eval₂ b x (invert (toLaurent (Polynomial.C a))) = _
      simp
    · change LaurentPolynomial.eval₂ b x (invert (toLaurent (Polynomial.X : R[X]))) = _
      simp
  have equiv (i : Bool) : e ≫ (lineArrow R i ≫ inclusion R i) = e ≫ WidePushout.head (lineArrow R) := by
    rw [WidePushout.arrow_ι]
  rw [point, point, ← left, ← right, Category.assoc, Category.assoc, equiv, equiv]

theorem point_changeChart {S : Type} [CommRing S] (b : R →+* S) (x : Sˣ) (i : Bool) :
    point R b (x : S) i = point R b (↑x⁻¹ : S) (!i) := by
  cases i
  · exact point_invert R b x
  · simpa using (point_invert R b x⁻¹).symm

/-- Over any local ring a section uses one of the two standard charts. -/
theorem exists_chart {S : Type} [CommRing S] [IsLocalRing S] (m : Spec (.of S) ⟶ projectiveLine R) :
    ∃ i : Bool, ∃ q : Spec (.of S) ⟶ Spec (.of R[X]), q ≫ inclusion R i = m := by
  let 𝒰 := lineCover R
  let j := 𝒰.idx (m (IsLocalRing.closedPoint S))
  have h : Set.range m ⊆ (𝒰.f j).opensRange := by
    rintro _ ⟨x,rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map m.continuous).mem_open
      (𝒰.f j).opensRange.2 (𝒰.covers _)
  obtain ⟨j',q,hq⟩ : ∃ j : WidePushoutShape Bool, ∃ q : Spec (.of S) ⟶ (lineDiagram R).obj j,
      q ≫ colimit.ι (lineDiagram R) j = m :=
    ⟨j,IsOpenImmersion.lift _ _ h, IsOpenImmersion.lift_fac _ _ h⟩
  -- use the chart containing the closed point, admitting also the overlap.
  cases j' with
  | none => exact ⟨false, q ≫ lineArrow R false, by rw [Category.assoc, WidePushout.arrow_ι]; exact hq⟩
  | some i => exact ⟨i, q, hq⟩

/-- The ring map and the affine coordinate determine a chart point uniquely. -/
theorem exists_coordinates {S : Type} [CommRing S] [IsLocalRing S]
    (b : R →+* S) (m : Spec (.of S) ⟶ projectiveLine R) (hm : m ≫ lineStructure R = Spec.map (CommRingCat.ofHom b)) :
    ∃ i : Bool, ∃ x : S, point R b x i = m := by
  obtain ⟨i,q,hq⟩ := exists_chart R m
  let φ := (Spec.preimage q).hom
  have hq' : Spec.map (CommRingCat.ofHom φ) = q := Spec.map_preimage q
  have hb : (φ.comp Polynomial.C) = b := by
    refine congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of S => m.hom) ?_
    apply Spec.map_injective
    calc
      Spec.map (CommRingCat.ofHom (φ.comp Polynomial.C)) = q ≫ scalarMap R R[X] := by
        rw [← hq']
        change Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp]; rfl
      _ = Spec.map (CommRingCat.ofHom b) := by
        rw [← inclusion_structure R i, ← Category.assoc, hq, hm]
  refine ⟨i, φ Polynomial.X, ?_⟩
  have e : Polynomial.eval₂RingHom b (φ Polynomial.X) = φ := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa using (congrArg (fun F : R →+* S => F r) hb).symm
    · simp
  rw [point, e, hq', hq]

/-- The two glued standard charts intersect only on the Laurent chart. -/
theorem intersection {p q : Spec (.of R[X])} (H : inclusion R false p = inclusion R true q) :
    ∃ z : Spec (.of (LaurentPolynomial R)), lineArrow R false z = p ∧ lineArrow R true z = q := by
  obtain ⟨k,a,b,z,ha,hb⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (lineDiagram R)
    (i := some false) (j := some true)).mp H
  cases k with
  | none =>
    have ae : a = WidePushoutShape.Hom.init false := Subsingleton.elim _ _
    have be : b = WidePushoutShape.Hom.init true := Subsingleton.elim _ _
    subst a
    subst b
    exact ⟨z,ha,hb⟩
  | some k =>
    have src {i j : Bool} (w : WidePushoutShape.Hom (some i) (some j)) : i = j := by
      cases w; rfl
    have bad : false = true := (src a).symm.trans (src b)
    cases bad

/-- Equality of two chart coordinates on the same affine chart. -/
theorem point_injective {S : Type} [CommRing S] (b : R →+* S) (i : Bool) :
    Function.Injective (fun x : S => point R b x i) := by
  intro x y h
  have e : Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom b x)) =
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom b y)) := by
    apply (cancel_mono (inclusion R i)).mp
    exact h
  have e' := congrArg (fun t : CommRingCat.of R[X] ⟶ CommRingCat.of S => t.hom Polynomial.X)
    (Spec.map_injective e)
  simpa using e'

/-- A field-valued point in both charts has nonzero finite coordinate. -/
theorem cross_nonzero {K : Type} [Field K] (b : R →+* K) {x y : K}
    (h : point R b x false = point R b y true) : x ≠ 0 := by
  let t := IsLocalRing.closedPoint K
  obtain ⟨z,hz,_⟩ := intersection R (congrArg (fun m : Spec (.of K) ⟶ projectiveLine R => m t) h)
  have free : (Polynomial.X : R[X]) ∉ (lineArrow R false z).asIdeal := by
    change toLaurent (Polynomial.X : R[X]) ∉ z.asIdeal
    rw [Polynomial.toLaurent_X]
    exact z.asIdeal.notMem_of_isUnit (isUnit_T 1)
  rw [hz] at free
  intro x0
  change Polynomial.eval₂ b x Polynomial.X ∉ t.asIdeal at free
  exact free (by simp [x0])

theorem cross_product {K : Type} [Field K] (b : R →+* K) {x y : K}
    (h : point R b x false = point R b y true) : x * y = 1 := by
  have hx := cross_nonzero R b h
  have h' := (point_invert R b (Units.mk0 x hx)).symm.trans h
  have yx : x⁻¹ = y := point_injective R b true h'
  rw [← yx, mul_inv_cancel₀ hx]

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.point_changeChart
#print axioms ZInQBlueprint.BinaryCover.exists_coordinates
#print axioms ZInQBlueprint.BinaryCover.cross_product
