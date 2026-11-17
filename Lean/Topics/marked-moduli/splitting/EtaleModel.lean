import VerticalSplitting
import ComponentFields
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Etale.Basic

/-! The diagonal idempotent turns equality after reduction into equality of lifts. -/
namespace MarkedModuli.Splitting
open scoped TensorProduct
open IsLocalRing Algebra

/-- Two integral points of an unramified, essentially finite type algebra
in a local domain coincide when their reductions coincide. -/
theorem unramified_lifts_unique (R B V : Type*) [CommRing R] [CommRing B] [CommRing V]
    [Algebra R B] [Algebra R V] [EssFiniteType R B] [FormallyUnramified R B]
    [IsDomain V] [IsLocalRing V] (f g : B →ₐ[R] V)
    (same : ∀ b, residue V (f b) = residue V (g b)) : f = g := by
  obtain ⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧
      KaehlerDifferential.ideal R B = Ideal.span {e} :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R B)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <|
        inferInstanceAs (Subsingleton (KaehlerDifferential R B))
  let φ : (B ⊗[R] B) →ₐ[R] V := Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)
  have red (t : B ⊗[R] B) :
      residue V (φ t) = residue V (f (Algebra.TensorProduct.lmul' R t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp [φ, same]
    | add _ _ hx hy => simp only [map_add]; rw [hx, hy]
  have hμ : Algebra.TensorProduct.lmul' R e = 0 := by
    change e ∈ KaehlerDifferential.ideal R B
    rw [hsp]
    exact Ideal.subset_span (Set.mem_singleton e)
  have hzero : residue V (φ e) = 0 := by rw [red, hμ, map_zero, map_zero]
  have he' : IsIdempotentElem (φ e) := he.map φ
  have hφ : φ e = 0 := (IsIdempotentElem.iff_eq_zero_or_one.mp he').resolve_right (by
    intro h; simp [h] at hzero)
  have kerLe : KaehlerDifferential.ideal R B ≤ RingHom.ker φ.toRingHom := by
    rw [hsp, Ideal.span_singleton_le_iff_mem]
    exact hφ
  ext b
  have hb : φ (1 ⊗ₜ[R] b - b ⊗ₜ[R] 1) = 0 :=
    kerLe (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b)
  exact (show g b = f b from by simpa [φ, sub_eq_zero] using hb).symm


section Model
variable {R B F Ω : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Field F] [Field Ω] [Algebra R F] [Algebra F Ω] [Algebra R Ω] [IsScalarTower R F Ω]

/-- Finite over the base ring, every value of an integral-model point belongs
to the chosen extension valuation ring. -/
def integralValueHom (v : ValuationSubring Ω) [Algebra R v] [IsScalarTower R v Ω]
    [Module.Finite R B] (y : B →ₐ[R] Ω) : B →ₐ[R] v where
  toFun b := ⟨y b, by
    have hR : IsIntegral R (y b) := (Algebra.IsIntegral.isIntegral (R := R) b).map y
    have hV : IsIntegral v (y b) := hR.tower_top
    obtain ⟨z,hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hV
    exact hz ▸ z.2⟩
  map_one' := Subtype.ext y.map_one
  map_mul' _ _ := Subtype.ext (y.map_mul _ _)
  map_zero' := Subtype.ext y.map_zero
  map_add' _ _ := Subtype.ext (y.map_add _ _)
  commutes' r := Subtype.ext ((y.commutes r).trans (IsScalarTower.algebraMap_apply R v Ω r))

/-- For the actual generic fibre of a finite unramified model, valuation inertia
fixes every geometric point, including points on distinct connected components. -/
theorem integralModel_inertia (v : ValuationSubring Ω) [Algebra R v] [IsScalarTower R v Ω]
    [Module.Finite R B] [FormallyUnramified R B] :
    inertia F v ≤ (pointAction F Ω (F ⊗[R] B)).ker := by
  rintro g ⟨d,hd,rfl⟩
  apply MonoidHom.mem_ker.mpr
  apply Equiv.ext
  intro x
  let baseChange := Algebra.TensorProduct.liftEquivRight R F B Ω
  let y := baseChange.symm x
  let y' := baseChange.symm (pointAction F Ω (F ⊗[R] B) d.1 x)
  have same (b : B) : residue v (integralValueHom v y' b) = residue v (integralValueHom v y b) := by
    have he : d • (integralValueHom v y b) = integralValueHom v y' b := Subtype.ext rfl
    rw [← he]
    exact inertia_residue F v d hd _
  have equal := unramified_lifts_unique R B v (integralValueHom v y') (integralValueHom v y) same
  apply baseChange.symm.injective
  ext b
  exact congrArg Subtype.val (DFunLike.congr_fun equal b)

/-- An integral finite étale model implies that the literal splitting subfield
of the full generic fibre lies in the chosen inertia fixed field. -/
theorem finiteEtaleModel_splitting (v : ValuationSubring Ω) [Algebra R v] [IsScalarTower R v Ω]
    [Module.Finite R B] [Etale R B] [IsGalois F Ω] :
    IntermediateField.fixedField (pointAction F Ω (F ⊗[R] B)).ker = pointField F Ω (F ⊗[R] B) ∧
    Module.Finite F (pointField F Ω (F ⊗[R] B)) ∧ IsGalois F (pointField F Ω (F ⊗[R] B)) ∧
    pointField F Ω (F ⊗[R] B) ≤ IntermediateField.fixedField (inertia F v) := by
  have h := etale_pointField (A := F ⊗[R] B) F Ω
  refine ⟨fixedField_pointAction F Ω _, h.1, h.2, ?_⟩
  intro z hz
  apply (IntermediateField.mem_fixedField_iff _ _).mpr
  intro g hg
  have hm := integralModel_inertia (R := R) (F := F) (B := B) v hg
  rw [pointAction_kernel] at hm
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hm z hz


/-- A finite étale marking algebra may dominate a different fibre. It suffices
that *every* geometric point of that fibre be defined over the field of markings. -/
theorem fieldOfMarkings_transfer (v : ValuationSubring Ω) [Algebra R v] [IsScalarTower R v Ω]
    [Module.Finite R B] [Etale R B] [IsGalois F Ω] (A : Type*) [CommRing A] [Algebra F A]
    (mark : ∀ x : Points F Ω A, ∃ y : A →ₐ[F] pointField F Ω (F ⊗[R] B),
      (pointField F Ω (F ⊗[R] B)).val.comp y = x) :
    pointField F Ω A ≤ IntermediateField.fixedField (inertia F v) :=
  ((pointField_le_iff_lifts F Ω A _).mpr mark).trans
    (finiteEtaleModel_splitting (R := R) (F := F) (B := B) v).2.2.2

end Model


/-- Specialization to the base valuation ring obtained by restricting the chosen
prolongation. It applies, in particular, when that base valuation is discrete. -/
theorem valuationRing_model {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    (v : ValuationSubring Ω) (B : Type*) [CommRing B] [Algebra (v.comap (algebraMap F Ω)) B]
    [Module.Finite (v.comap (algebraMap F Ω)) B] [Etale (v.comap (algebraMap F Ω)) B] :
    pointField F Ω (F ⊗[↥(v.comap (algebraMap F Ω))] B) ≤ IntermediateField.fixedField (inertia F v) := by
  let R := v.comap (algebraMap F Ω)
  let i : R →+* Ω := (algebraMap F Ω).comp (algebraMap R F)
  let j : R →+* v := i.codRestrict v.toSubring (fun a ↦ a.2)
  let : Algebra R Ω := i.toAlgebra
  let : Algebra R v := j.toAlgebra
  have : IsScalarTower R F Ω := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R v Ω := IsScalarTower.of_algebraMap_eq' rfl
  exact (finiteEtaleModel_splitting (R := ↥R) (F := F) (B := B) v).2.2.2

end MarkedModuli.Splitting

#print axioms MarkedModuli.Splitting.unramified_lifts_unique
#print axioms MarkedModuli.Splitting.integralModel_inertia
#print axioms MarkedModuli.Splitting.finiteEtaleModel_splitting
#print axioms MarkedModuli.Splitting.fieldOfMarkings_transfer
#print axioms MarkedModuli.Splitting.valuationRing_model
