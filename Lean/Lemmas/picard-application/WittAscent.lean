import PicardGoodReduction

/-! Enlargement of the finite unramified field used by a local power quotient. -/
open CategoryTheory AlgebraicGeometry
open ZInQBlueprint.AbelianModel
open ZOverQ.Qualitative.LocalSupport ZOverQ.Qualitative.Picard.Assembly
open ZOverQ.Qualitative.PicardDescent ZOverQ.Qualitative.PicardConjugation
open ZOverQ.Qualitative.PicardLocalization ZOverQ.Qualitative.PicardGoodReduction
open ZInQ ZInQ.QualitativeHeight

namespace ZOverQ.Qualitative.WittAscent
noncomputable section

/-- Coherence of successive scalar extensions as commutative group schemes. -/
def baseChangeCompIso {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (A : GroupScheme R) :
    (baseChange (g.comp f)).obj A ≅ (baseChange g).obj ((baseChange f).obj A) := by
  let a := Spec.map (CommRingCat.ofHom f)
  let b := Spec.map (CommRingCat.ofHom g)
  have H : Spec.map (CommRingCat.ofHom (g.comp f)) = b ≫ a :=
    Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)
  let e : Over.pullback (Spec.map (CommRingCat.ofHom (g.comp f))) ≅ Over.pullback a ⋙ Over.pullback b := by
    rw [H]
    exact Over.pullbackComp b a
  exact (Functor.mapCommGrpNatIso e).app A ≪≫ Functor.mapCommGrpCompIso.app A

variable (p : ℕ) [Fact p.Prime] {k l : Subfield (Residues p)}

/-- Coordinatewise extension from a residue subfield to a larger one. -/
def wittInclusion (h : k ≤ l) : WittVector p k →+* WittVector p l :=
  WittVector.map (Subfield.inclusion h)

private theorem wittInclusion_inj (h : k ≤ l) : Function.Injective (wittInclusion p h) :=
  WittVector.map_injective _ (Subfield.inclusion h).injective

/-- The induced embedding of the two local fraction fields. -/
def fractionInclusion (h : k ≤ l) : FractionRing (WittVector p k) →+* FractionRing (WittVector p l) :=
  IsFractionRing.lift (g := (algebraMap (WittVector p l) (FractionRing (WittVector p l))).comp (wittInclusion p h))
    ((IsFractionRing.injective (WittVector p l) _).comp (wittInclusion_inj p h))

theorem fractionInclusion_integer (h : k ≤ l) (x : WittVector p k) :
    fractionInclusion p h (algebraMap (WittVector p k) _ x) =
      algebraMap (WittVector p l) _ (wittInclusion p h x) := IsFractionRing.lift_algebraMap _ _

private theorem wittInclusion_padic (h : k ≤ l) (x : ℤ_[p]) :
    wittInclusion p h (fromPadics p k x) = fromPadics p l x := by
  let fk : ZMod p →+* k := ZMod.castHom (by simp) k
  let fl : ZMod p →+* l := ZMod.castHom (by simp) l
  have eqn : (Subfield.inclusion h).comp fk = fl := Subsingleton.elim _ _
  apply WittVector.ext
  intro n
  exact RingHom.congr_fun eqn (((WittVector.equiv p).symm x).coeff n)

private theorem padic_integer (F : Subfield (Residues p)) [Finite F] (x : ℤ_[p]) :
    letI := wittFractionAlgebra p F
    algebraMap ℚ_[p] (FractionRing (WittVector p F)) (algebraMap ℤ_[p] ℚ_[p] x) =
      algebraMap (WittVector p F) _ (fromPadics p F x) := IsFractionRing.lift_algebraMap _ _

/-- The fraction-field embedding respects the canonical maps from `ℚ_p`. -/
theorem fractionInclusion_over_padics [Finite k] [Finite l] (h : k ≤ l) :
    letI := wittFractionAlgebra p k
    letI := wittFractionAlgebra p l
    (fractionInclusion p h).comp (algebraMap ℚ_[p] (FractionRing (WittVector p k))) =
      algebraMap ℚ_[p] (FractionRing (WittVector p l)) := by
  let := wittFractionAlgebra p k
  let := wittFractionAlgebra p l
  apply IsFractionRing.ringHom_ext (A := ℤ_[p])
  intro x
  change fractionInclusion p h ((algebraMap ℚ_[p] _) (algebraMap ℤ_[p] ℚ_[p] x)) = _
  rw [padic_integer p k, padic_integer p l, fractionInclusion_integer, wittInclusion_padic]

/-- The enlargement as a morphism of the actual `ℚ_p`-algebras. -/
def fractionAlgHom [Finite k] [Finite l] (h : k ≤ l) :
    letI := wittFractionAlgebra p k
    letI := wittFractionAlgebra p l
    FractionRing (WittVector p k) →ₐ[ℚ_[p]] FractionRing (WittVector p l) := by
  let := wittFractionAlgebra p k
  let := wittFractionAlgebra p l
  exact ⟨fractionInclusion p h, RingHom.congr_fun (fractionInclusion_over_padics p h)⟩

/-- Base change of the integral abelian scheme is an abelian model after enlarging the Witt ring. -/
theorem goodWitt_mono (h : k ≤ l) {J : GroupScheme (FractionRing (WittVector p k))}
    (good : GoodWitt p k J) : GoodWitt p l ((baseChange (fractionInclusion p h)).obj J) := by
  let i := wittInclusion p h
  let j := fractionInclusion p h
  let a := algebraMap (WittVector p k) (FractionRing (WittVector p k))
  let b := algebraMap (WittVector p l) (FractionRing (WittVector p l))
  have square : b.comp i = j.comp a := RingHom.ext (fun x => (fractionInclusion_integer p h x).symm)
  obtain ⟨M,hM,⟨e⟩⟩ := good
  refine ⟨(baseChange i).obj M,isAbelianScheme_baseChange i hM,⟨?_⟩⟩
  exact (baseChangeCompIso i b M).symm ≪≫ eqToIso (congrArg (fun f => (baseChange f).obj M) square) ≪≫
    baseChangeCompIso a j M ≪≫ (baseChange j).mapIso e

/-- Over the larger field the good object is the direct scalar extension of the same global Jacobian. -/
theorem goodWitt_localized_mono {R : Type} [CommRing R] (h : k ≤ l) (A : GroupScheme R)
    (φ : R →+* FractionRing (WittVector p k)) (good : GoodWitt p k ((baseChange φ).obj A)) :
    GoodWitt p l ((baseChange ((fractionInclusion p h).comp φ)).obj A) :=
  goodWitt_of_iso (baseChangeCompIso φ (fractionInclusion p h) A).symm (goodWitt_mono p h good)

private abbrev wittCharZero (F : Subfield (Residues p)) : CharZero (WittVector p F) :=
  charZero_of_injective_ringHom (f := fromPadics p F)
    ((WittVector.map_injective _ (ZMod.castHom (by simp) F).injective).comp (WittVector.equiv p).symm.injective)

private theorem rational_twist_nonzero (s : ℚ) : ((PrimitiveTwist.twist s : ℤ) : ℚ) ≠ 0 := by
  exact_mod_cast (PrimitiveTwist.positive s).ne'

/-- The one field selected by the cluster calculation works in every larger finite unramified
field. The quotient is a morphism over that larger field from the actual scalar-extended Jacobian. -/
theorem family_reduction_after_enlargement (criterion : SplitSexticDDMM) (hp : 3 < p) (st : SerreTateAt p)
    (t : ℚ) (ht : t ∉ contactSet) (hev : ¬ Odd (padicValRat p (primitiveBranch (picardParameter t)))) :
    let s := picardParameter t
    let e : ℤ := PrimitiveTwist.twist s
    ∃ (q : PicardLocal.WittRing p) (A : Finset (Fin 2)) (m : ℕ) (D : FibreData p s.num s.den e q A m),
      let k := D.finiteModel.field
      letI : Finite k := D.finiteModel.finite
      letI := wittCharZero p k
      let S := WittVector p k
      let K := FractionRing S
      let J := familyJacobian t (e:ℚ) ht (rational_twist_nonzero s) (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)
      ∃ φ : fixedField →ₐ[ℚ] K, φ ρ = algebraMap S K D.finiteModel.rho ∧
        ∀ (l : Subfield (Residues p)) [Finite l] (h : k ≤ l),
          let Jl := (baseChange ((fractionInclusion p h).comp φ.toRingHom)).obj J
          GoodWitt p l Jl ∧ ∀ (B : GroupScheme ℚ), IsAbelianScheme B → ∀ (n : ℕ),
            LocalPowerQuotient p l Jl n B → GoodReductionAt p B := by
  let s := picardParameter t
  let e : ℤ := PrimitiveTwist.twist s
  let J := familyJacobian t (e:ℚ) ht (rational_twist_nonzero s) (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)
  obtain ⟨q,A,m,D,_,φ,hφ,good⟩ := family_goodWitt criterion p hp t ht hev
  let k := D.finiteModel.field
  let : Finite k := D.finiteModel.finite
  let := wittCharZero p k
  refine ⟨q,A,m,D,φ,hφ,?_⟩
  intro l fin h
  let j := (fractionInclusion p h).comp φ.toRingHom
  have model : GoodWitt p l ((baseChange j).obj J) := goodWitt_localized_mono p h J φ.toRingHom good
  have hJ : IsAbelianScheme J := by unfold J familyJacobian; apply jacobian_is_abelian
  exact ⟨model,fun B hB n onto => AbelianPowers.reduction_of_power p st hB l n _
    (isAbelianScheme_baseChange j hJ) model onto⟩

#print axioms baseChangeCompIso
#print axioms fractionInclusion_over_padics
#print axioms fractionAlgHom
#print axioms goodWitt_mono
#print axioms goodWitt_localized_mono
#print axioms family_reduction_after_enlargement

end
end ZOverQ.Qualitative.WittAscent
