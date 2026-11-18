import WittAscent
import CommonWittReduction
import GeneralQuaternionField
import IsogenyHeight

/-! A polynomial defining the integers from the global rational variety,
its quaternion action, a global isogeny and the canonical polarized moduli point. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ZInQBlueprint.NormalDescent
open scoped ZInQBlueprint.NormalDescent TensorProduct
open ZInQBlueprint.AbelianModel ZInQBlueprint.ThetaQuotient
open ZOverQ.Qualitative.Picard.Assembly ZOverQ.Qualitative.Picard
open ZOverQ.Qualitative.LocalSupport ZOverQ.Qualitative.PicardGoodReduction
open ZOverQ.Qualitative.PicardLocalization ZOverQ.Qualitative.PicardDescent
open ZOverQ.Qualitative.PicardConjugation ZInQ ZInQ.QualitativeHeight
namespace ZOverQ.Qualitative.PicardPolynomial
noncomputable section

/-- The algebraic data supplied by Guitart's rational variety and its
endomorphism theorem. The two endomorphisms are elements of the actual
rational endomorphism ring of this group scheme. -/
structure QuaternionVariety (E : Type) [Field E] [NumberField E] where
  B : GroupScheme ℚ
  abelian : IsAbelianScheme B
  dimension : SmoothOfRelativeDimension (2 * Module.finrank ℚ E) B.X.hom
  [nontrivialEnd : Nontrivial (ℚ ⊗[ℤ] End B)]
  [centralScalars : Algebra E (ℚ ⊗[ℤ] End B)]
  [tower : IsScalarTower ℚ E (ℚ ⊗[ℤ] End B)]
  i : ℚ ⊗[ℤ] End B
  j : ℚ ⊗[ℤ] End B
  sq_i : i^2 = -3
  sq_j : j^2 = 2
  skew : j*i = -(i*j)

theorem QuaternionVariety.fieldAction {E : Type} [Field E] [NumberField E] (V : QuaternionVariety E) :
    HasGL2Type V.B (2 * Module.finrank ℚ E) := by
  let := V.nontrivialEnd
  let := V.centralScalars
  let := V.tower
  exact GeneralQuaternionField.field_action (E := E) V.i V.j V.sq_i V.sq_j V.skew

/-- The inverse coordinate outside the discarded point s=5 preserves the
primitive branch divisor and supplies a noncontact parameter. -/
theorem parameter_preimage {s : ℚ} (hs : s ≠ 5) (hb : primitiveBranch s ≠ 0) :
    ∃ t : ℚ, t ∉ contactSet ∧ picardParameter t = s := by
  let t := 120 / (s-5)
  have hd : s-5 ≠ 0 := sub_ne_zero.mpr hs
  have hn : t ≠ 0 := div_ne_zero (by norm_num) hd
  have back : picardParameter t = s := by unfold picardParameter t; field_simp; ring
  refine ⟨t,?_,back⟩
  intro hc
  have z : Mult.contactPoly t=0 := by
    rw [Mult.contactPoly_eq_prod]
    exact Finset.prod_eq_zero hc (sub_self _)
  have eqn := branchForm_change hn (s.den:ℚ)
  rw [back,Rat.mul_den_eq_num,z,mul_zero,mul_zero] at eqn
  exact hb eqn

private theorem twist_ne (s : ℚ) : ((PrimitiveTwist.twist s : ℤ) : ℚ) ≠ 0 := by
  exact_mod_cast (PrimitiveTwist.positive s).ne'

/-- The actual squarefree twist of the Picard Jacobian in the coordinate t. -/
def twistedJacobian (t : ℚ) (ht : t ∉ contactSet) : GroupScheme fixedField :=
  familyJacobian t ((PrimitiveTwist.twist (picardParameter t) : ℤ) : ℚ) ht (twist_ne _)
    (AlgEquiv.refl : fixedField ≃ₐ[ℚ] fixedField)

theorem twistedJacobian_abelian (t : ℚ) (ht : t ∉ contactSet) : IsAbelianScheme (twistedJacobian t ht) := by
  unfold twistedJacobian familyJacobian
  apply jacobian_is_abelian

/-- The fixed-field power quotient has source the actual Picard Jacobian. -/
def GlobalPowerQuotient {M : Type} [Field M] [NumberField M] (ψ : fixedField →ₐ[ℚ] M)
    (t : ℚ) (ht : t ∉ contactSet) (n : ℕ) (B : GroupScheme ℚ) : Prop :=
  let J := twistedJacobian t ht
  ∃ f : AbelianPowers.power ((baseChange ψ.toRingHom).obj J) n ⟶ (baseChange (algebraMap ℚ M)).obj B,
    AlgebraicGeometry.Surjective f.hom.hom.hom.left

/-- Scheme-theoretic surjectivity of a group homomorphism survives scalar extension. -/
theorem surjective_baseChange {R S : Type} [CommRing R] [CommRing S] (h : R →+* S)
    {A B : GroupScheme R} (f : A ⟶ B) (onto : AlgebraicGeometry.Surjective f.hom.hom.hom.left) :
    AlgebraicGeometry.Surjective ((baseChange h).map f).hom.hom.hom.left := by
  let a := Spec.map (CommRingCat.ofHom h)
  let p := pullback.fst A.X.hom a
  let q := pullback.fst B.X.hom a
  let g := f.hom.hom.hom
  let j := ((Over.pullback a).map g).left
  have pf : j ≫ q = p ≫ g.left := pullback.lift_fst ..
  have ps : j ≫ pullback.snd B.X.hom a = pullback.snd A.X.hom a := pullback.lift_snd ..
  have hs : IsPullback j p q g.left := by
    apply IsPullback.of_right _ _ (IsPullback.of_hasPullback B.X.hom a).flip
    · rw [ps,g.w]
      exact (IsPullback.of_hasPullback A.X.hom a).flip
    · exact pf
  exact MorphismProperty.of_isPullback hs.flip onto

/-- Base change of one global power quotient gives the required local map for
every embedding of its coefficient field in a finite unramified extension. -/
theorem local_of_global (p : ℕ) [Fact p.Prime] (k : Subfield (Residues p)) [Finite k]
    {M : Type} [Field M] [NumberField M] (ψ : fixedField →ₐ[ℚ] M)
    (t : ℚ) (ht : t ∉ contactSet) (n : ℕ) (B : GroupScheme ℚ) (h : GlobalPowerQuotient ψ t ht n B) :
    letI := CommonWittField.wittCharZero p k
    let K := FractionRing (WittVector p k)
    let J := twistedJacobian t ht
    ∀ i : M →ₐ[ℚ] K, LocalPowerQuotient p k ((baseChange (i.comp ψ).toRingHom).obj J) n B := by
  let := CommonWittField.wittCharZero p k
  let := wittFractionAlgebra p k
  let K := FractionRing (WittVector p k)
  let J := twistedJacobian t ht
  change ∀ i : M →ₐ[ℚ] K, LocalPowerQuotient p k ((baseChange (i.comp ψ).toRingHom).obj J) n B
  intro i
  obtain ⟨f,onto⟩ := h
  let F := baseChange i.toRingHom
  let e := AbelianPowers.baseChangePowerIso i.toRingHom (WittAscent.baseChangeCompIso ψ.toRingHom i.toRingHom J).symm n
  let a := algebraMap ℚ M
  let b := algebraMap ℚ ℚ_[p]
  let c := algebraMap ℚ_[p] K
  let d := (WittAscent.baseChangeCompIso a i.toRingHom B).symm ≪≫
    eqToIso (congrArg (fun g : ℚ →+* K => (baseChange g).obj B)
      (Subsingleton.elim (i.toRingHom.comp a) (c.comp b))) ≪≫ WittAscent.baseChangeCompIso b c B
  let U := CommGrp.forget (Over (Spec (.of K))) ⋙ Over.forget _
  refine ⟨e.inv ≫ F.map f ≫ d.hom, ?_⟩
  change AlgebraicGeometry.Surjective (U.map (e.inv ≫ F.map f ≫ d.hom))
  have : AlgebraicGeometry.Surjective (U.map (F.map f)) := surjective_baseChange i.toRingHom f onto
  rw [Functor.map_comp,Functor.map_comp]
  infer_instance

/-- A uniform field of definition for the power quotient suffices. No choice of
a good-reduction model, local isogeny, or field of GL₂-type is an input on a fibre. -/
theorem integer_polynomial_of_quaternionic_fibres
    {K : Type} [Field K] [NumberField K] {n m : ℕ} (P : InvariantCharts K n m)
    (M : Type) [Field M] [NumberField M] [Normal ℚ M] (ψ : fixedField →ₐ[ℚ] M)
    (hF : GroupScheme ℚ → ℝ) (vk : VonKanel hF) (criterion : SplitSexticDDMM)
    (st : ∀ (p : ℕ) [Fact p.Prime], SerreTateAt p)
    (D : ℕ) (u v : ℝ) (hu : 0 ≤ u) (except : Finset ℚ)
    (fibres : ∀ (t : ℚ) (ht : t ∉ contactSet), picardParameter t ∉ except →
      ∃ (E : Type) (_ : Field E) (_ : NumberField E) (V : QuaternionVariety E) (z : Fin n → K),
        Module.finrank ℚ E ≤ D ∧ GlobalPowerQuotient ψ t ht (Module.finrank ℚ E - 1) V.B ∧
        P.Represents z (igusaRatio (chart (picardParameter t))) ∧
        normalizedHeight z ≤ u * max 1 (hF V.B) + v)
    (tian : ZInQBlueprint.OriginalRank.PublishedGenusRows.PublishedTian47)
    (grossZagier : ZOverQ.Bounded.SimpleZeroRank) : IntegerPolynomial := by
  obtain ⟨S,primes,h₂,h₃,reduce⟩ := CommonWittReduction.good_reduction_of_clusters M ψ
  apply integer_polynomial_of_moduli_charts P hF vk (2*D) u v hu S (insert 5 except) primes h₂ h₃ _ tian grossZagier
  intro s outside branch
  have s₅ : s ≠ 5 := fun h => outside (Finset.mem_insert.mpr (Or.inl h))
  have good : s ∉ except := fun h => outside (Finset.mem_insert_of_mem h)
  obtain ⟨t,ht,back⟩ := parameter_preimage s₅ branch
  subst s
  obtain ⟨E,_,_,V,z,cap,quotient,form,height⟩ := fibres t ht good
  let n' := Module.finrank ℚ E - 1
  have maps (p : ℕ) [Fact p.Prime] : CommonWittReduction.LocalPowerMaps p M ψ t ht V.B n' := by
    dsimp only [CommonWittReduction.LocalPowerMaps]
    intro q A m D hq
    let := D.finiteModel.finite
    let := CommonWittField.wittCharZero p D.finiteModel.field
    intro i _
    exact local_of_global p D.finiteModel.field ψ t ht n' V.B quotient i
  let factor : RationalFactor (2 * Module.finrank ℚ E) S (picardParameter t) :=
    ⟨V.B,V.abelian,V.dimension,V.fieldAction,
      fun p _ _ away => reduce p away criterion (st p) t ht V.B V.abelian n' (maps p)⟩
  refine ⟨_,factor,z,?_,?_,form,height⟩
  · have := Module.finrank_pos (R:=ℚ) (M:=E)
    omega
  · omega

/-- Descent for the twisted family away from finitely many rational parameters. -/
def MarkedIsogenies {M : Type} [Field M] [NumberField M] (ψ : fixedField →ₐ[ℚ] M)
    (D : ℕ) (except : Finset ℚ) : Prop :=
  ∀ (t : ℚ) (ht : t ∉ contactSet), picardParameter t ∉ except →
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (V : QuaternionVariety E),
      Module.finrank ℚ E ≤ D ∧
      let A := AbelianPowers.power ((baseChange ψ.toRingHom).obj (twistedJacobian t ht)) (Module.finrank ℚ E - 1)
      let B := (baseChange (algebraMap ℚ M)).obj V.B
      ∃ f : A ⟶ B, IsogenyHeight.IsIsogeny (M := M) (A := A) (B := B) f

/-- The projective height of the canonical polarized Jacobian in fixed moduli charts. -/
def PolarizedModuliHeight {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    {n m : ℕ} (P : InvariantCharts K n m) (ψ : fixedField →ₐ[ℚ] M) (F : GroupScheme M → ℝ)
    (except : Finset ℚ) (u v : ℝ) : Prop :=
  ∀ (t : ℚ) (ht : t ∉ contactSet), picardParameter t ∉ except → ∃ z : Fin n → K,
    P.Represents z (igusaRatio (chart (picardParameter t))) ∧
    normalizedHeight z ≤ u * max 1 (F ((baseChange ψ.toRingHom).obj (twistedJacobian t ht))) + v

set_option maxHeartbeats 1000000 in
/-- The qualitative polynomial theorem from two independent family applications.
Descent supplies the marked rational variety and one isogeny over M. The moduli
comparison concerns the canonical polarized Jacobian alone. Scalar extension,
the change of stable height, and all local reductions are deduced. -/
theorem integer_polynomial_of_picard_jacobians
    {K : Type} [Field K] [NumberField K] {n m : ℕ} (P : InvariantCharts K n m)
    (M : Type) [Field M] [NumberField M] [Normal ℚ M] (ψ : fixedField →ₐ[ℚ] M)
    (hF : GroupScheme ℚ → ℝ) (F : GroupScheme M → ℝ)
    (vk : VonKanel hF) (criterion : SplitSexticDDMM)
    (st : ∀ (p : ℕ) [Fact p.Prime], SerreTateAt p)
    (D : ℕ) (stable : IsogenyHeight.StableHeight F) (degree : IsogenyHeight.DegreeBound F (2*D))
    (extend : ∀ B : GroupScheme ℚ, IsAbelianScheme B → F ((baseChange (algebraMap ℚ M)).obj B) = hF B)
    (exceptDescent exceptModuli : Finset ℚ) (u v : ℝ) (hu : 0 ≤ u)
    (descent : MarkedIsogenies ψ D exceptDescent)
    (moduli : PolarizedModuliHeight P ψ F exceptModuli u v)
    (tian : ZInQBlueprint.OriginalRank.PublishedGenusRows.PublishedTian47)
    (grossZagier : ZOverQ.Bounded.SimpleZeroRank) : IntegerPolynomial := by
  obtain ⟨a,b,ha,bound⟩ := IsogenyHeight.uniform_power_bound F (2*D) stable degree
  apply integer_polynomial_of_quaternionic_fibres P M ψ hF vk criterion st D (u*a) (u*b+v)
    (mul_nonneg hu ha) (exceptDescent ∪ exceptModuli) _ tian grossZagier
  intro t ht good
  have good₁ : picardParameter t ∉ exceptDescent := fun h => good (Finset.mem_union_left _ h)
  have good₂ : picardParameter t ∉ exceptModuli := fun h => good (Finset.mem_union_right _ h)
  obtain ⟨E,_,_,V,cap,iso⟩ := descent t ht good₁
  obtain ⟨f,hf⟩ := iso
  obtain ⟨z,form,hz⟩ := moduli t ht good₂
  let J := (baseChange ψ.toRingHom).obj (twistedJacobian t ht)
  let B := (baseChange (algebraMap ℚ M)).obj V.B
  let g := 2 * Module.finrank ℚ E
  have hg₀ : 0 < g := by dsimp [g]; exact Nat.mul_pos (by decide) (Module.finrank_pos (R:=ℚ) (M:=E))
  have hg₁ : g ≤ 2*D := Nat.mul_le_mul_left 2 cap
  have dim : SmoothOfRelativeDimension g B.X.hom := by
    have : SmoothOfRelativeDimension g V.B.X.hom := V.dimension
    exact inferInstanceAs (SmoothOfRelativeDimension g (pullback.snd V.B.X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ M)))))
  have est := bound B J g (Module.finrank ℚ E - 1) hg₀ hg₁
    (isAbelianScheme_baseChange _ V.abelian) (isAbelianScheme_baseChange _ (twistedJacobian_abelian t ht)) dim ⟨f,hf⟩
  have hbase : F B = hF V.B := extend V.B V.abelian
  have finalBound : max 1 (F J) ≤ a * max 1 (hF V.B) + b :=
    est.trans_eq (congrArg (fun h : ℝ => a * max 1 h + b) hbase)
  have quotient : GlobalPowerQuotient ψ t ht (Module.finrank ℚ E - 1) V.B := ⟨f,hf.2⟩
  refine ⟨E,‹Field E›,‹NumberField E›,V,z,cap,quotient,form,?_⟩
  calc
    normalizedHeight z ≤ u * max 1 (F J) + v := hz
    _ ≤ u * (a * max 1 (hF V.B) + b) + v := add_le_add (mul_le_mul_of_nonneg_left finalBound hu) le_rfl
    _ = u*a*max 1 (hF V.B)+(u*b+v) := by ring

end
end ZOverQ.Qualitative.PicardPolynomial

#print axioms ZOverQ.Qualitative.PicardPolynomial.QuaternionVariety.fieldAction
#print axioms ZOverQ.Qualitative.PicardPolynomial.parameter_preimage

#print axioms ZOverQ.Qualitative.PicardPolynomial.surjective_baseChange
#print axioms ZOverQ.Qualitative.PicardPolynomial.local_of_global

#print axioms ZOverQ.Qualitative.PicardPolynomial.integer_polynomial_of_quaternionic_fibres

#print axioms ZOverQ.Qualitative.PicardPolynomial.twistedJacobian_abelian
#print axioms ZOverQ.Qualitative.PicardPolynomial.integer_polynomial_of_picard_jacobians
