import PrimitiveTwist
import PicardConjugation
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Local splitting of the Picard sextic

Witt Frobenius preserves the unordered pair of conjugate sextics in primitive
integral coordinates. Its action on their finite set of roots therefore has
finite order. On each Witt coordinate the fixed-point equation is an ordinary
finite-field equation. This descends all the Hensel lifts simultaneously.
-/

namespace ZOverQ.Qualitative.LocalSupport

open Polynomial IsLocalRing
open ZOverQ.Qualitative.PicardLocal
noncomputable section

section Descent

variable (p : ℕ) [Fact p.Prime]

abbrev Residues := AlgebraicClosure (ZMod p)

private def frob : WittRing p →+* WittRing p := WittVector.map (frobenius (Residues p) p)

/-- The subfield on which the indicated power of Frobenius is the identity. -/
def residueExtension (n : ℕ) : Subfield (Residues p) :=
  (iterateFrobenius (Residues p) p n).eqLocusField (RingHom.id _)

theorem residueExtension_finite {n : ℕ} (hn : 0 < n) : Finite (residueExtension p n) := by
  classical
  let P : (Residues p)[X] := X^(p^n)-X
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hdeg : 1 < p^n := one_lt_pow₀ hp hn.ne'
  have hP : P ≠ 0 := by
    intro h
    have d := congrArg natDegree (sub_eq_zero.mp h)
    simp only [natDegree_X_pow, natDegree_X] at d
    omega
  let val (x : residueExtension p n) : P.roots.toFinset :=
    ⟨(x : Residues p), Multiset.mem_toFinset.mpr ((mem_roots hP).mpr (by
      have hx : (x : Residues p)^(p^n) = x := x.property
      simpa [IsRoot, P, sub_eq_zero] using hx))⟩
  exact Finite.of_injective val (fun _ _ h => Subtype.ext (congrArg (fun z : P.roots.toFinset => (z : Residues p)) h))

/-- Inclusion of Witt rings is coordinatewise inclusion of the residue fields. -/
def inclusion (F : Subfield (Residues p)) : WittVector p F →+* WittRing p :=
  WittVector.map F.subtype

theorem inclusion_injective (F : Subfield (Residues p)) : Function.Injective (inclusion p F) :=
  WittVector.map_injective _ Subtype.val_injective

private theorem coeff_iterate (n : ℕ) (w : WittRing p) (j : ℕ) :
    (((frob p)^[n]) w).coeff j = iterateFrobenius (Residues p) p n (w.coeff j) := by
  rw [coe_iterateFrobenius]
  exact (show Function.Semiconj (fun x : WittRing p => x.coeff j) (frob p)
    (frobenius (Residues p) p) from fun _ => rfl).iterate_right n w

theorem mem_witt_range {n : ℕ} {w : WittRing p} (h : ((frob p)^[n]) w = w) :
    w ∈ Set.range (inclusion p (residueExtension p n)) := by
  refine ⟨WittVector.mk p (fun j => ⟨w.coeff j, ?_⟩), ?_⟩
  · change iterateFrobenius (Residues p) p n (w.coeff j) = w.coeff j
    rw [← coeff_iterate, h]
  · ext; rfl

/-- All roots of a nonzero Frobenius-invariant polynomial that exist in the
strict Witt ring already lie in one finite-residue Witt ring. -/
theorem finite_ring_for_roots (P : (WittRing p)[X]) (hP : P ≠ 0) (hf : P.map (frob p) = P) :
    ∃ n : ℕ, 0 < n ∧ ∀ w, P.IsRoot w → w ∈ Set.range (inclusion p (residueExtension p n)) := by
  classical
  let T := P.roots.toFinset
  let f : T → T := fun t => ⟨frob p t, Multiset.mem_toFinset.mpr ((mem_roots hP).mpr (by
    have h := (isRoot_of_mem_roots (Multiset.mem_toFinset.mp t.property)).map (f := frob p)
    rwa [hf] at h))⟩
  have hf' : Function.Injective f := fun _ _ h => Subtype.ext <|
    WittVector.map_injective _ (frobenius (Residues p) p).injective (congrArg Subtype.val h)
  let g : Equiv.Perm T := Equiv.ofBijective f hf'.bijective_of_finite
  let n := Fintype.card (Equiv.Perm T)
  have hpow : g^n = 1 := pow_card_eq_one
  have comp : Function.Semiconj (fun t : T => (t : WittRing p)) g (frob p) := fun _ => rfl
  refine ⟨n, Fintype.card_pos, fun w hw => mem_witt_range p ?_⟩
  let t : T := ⟨w, Multiset.mem_toFinset.mpr ((mem_roots hP).mpr hw)⟩
  have h := comp.iterate_right n t
  rw [← Equiv.Perm.coe_pow, hpow] at h
  exact h.symm

def upper {R : Type*} [CommRing R] (a b : ℤ) (ρ : R) : R := (a:R)+ρ*(b:R)
def lower {R : Type*} [CommRing R] (a b : ℤ) (ρ : R) : R := (a:R)-ρ*(b:R)

/-- Integral polynomial of the twist. On `2e y²=f` its ordinate is `2e y`. -/
def twisted {R : Type*} [CommRing R] (a b e : ℤ) (ρ : R) : R[X] :=
  C (2*(e:R)) * sextic ((upper a b ρ)^6) ((lower a b ρ)^6)

theorem sextic_scale {R : Type*} [CommRing R] (c U V : R) :
    sextic (c*U) (c*V) = C c*sextic U V := by
  simp only [sextic, quartic, map_mul]
  ring

/-- The integral homogeneous-coordinate twist differs from the affine chart
of the global Jacobian by this specified nonzero square in the ordinate. -/
theorem primitive_chart_scale {K : Type*} [Field K] [CharZero K]
    (s : ℚ) (e : ℤ) (he : e ≠ 0) (ρ : K) :
    let v := 2*(e:K)*(s.den:K)^3
    v ≠ 0 ∧ twisted s.num s.den e ρ =
      C (v^2)*sextic (((s:K)+ρ)^6/(2*(e:K))) (((s:K)-ρ)^6/(2*(e:K))) := by
  have he' : 2*(e:K) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast he)
  have hd : (s.den:K) ≠ 0 := by exact_mod_cast s.den_nz
  have hr : (s.num:K) = (s:K)*(s.den:K) := by exact_mod_cast (Rat.mul_den_eq_num s).symm
  have n : upper s.num (s.den:ℤ) ρ = ((s:K)+ρ)*(s.den:K) := by
    simp only [upper, Int.cast_natCast, hr]; ring
  have d : lower s.num (s.den:ℤ) ρ = ((s:K)-ρ)*(s.den:K) := by
    simp only [lower, Int.cast_natCast, hr]; ring
  have scale (x : K) : (x*(s.den:K))^6 =
      (2*(e:K)*(s.den:K)^6)*(x^6/(2*(e:K))) := by
    field_simp [he']
  refine ⟨mul_ne_zero he' (pow_ne_zero _ hd), ?_⟩
  rw [twisted, n, d, scale, scale, sextic_scale, ← mul_assoc, ← map_mul]
  congr 2
  ring

theorem coordinates_nonzero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (a b : ℤ) (hb : b ≠ 0) {ρ : R} (hρ : ρ^2 = -3) :
    upper a b ρ ≠ 0 ∧ lower a b ρ ≠ 0 := by
  have hpos : 0 < a^2 + 3*b^2 := by nlinarith [sq_nonneg a, sq_pos_of_ne_zero hb]
  have hnorm : upper a b ρ * lower a b ρ = ((a^2 + 3*b^2 : ℤ) : R) := by
    simp only [upper, lower, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    linear_combination -(b:R)^2*hρ
  have hn : upper a b ρ * lower a b ρ ≠ 0 := by rw [hnorm]; exact_mod_cast hpos.ne'
  exact ⟨left_ne_zero_of_mul hn, right_ne_zero_of_mul hn⟩

/-- The root `ρ` and all the roots of the actual integral sextic belong to
one finite-residue Witt ring. The degree of the residue extension may vary. -/
theorem finite_ring_for_family (a b : ℤ) (hb : b ≠ 0) {ρ : WittRing p} (hρ : ρ^2 = -3) :
    ∃ n : ℕ, 0 < n ∧ ρ ∈ Set.range (inclusion p (residueExtension p n)) ∧
      (∀ z : WittRing p, z^2 = -2 → z ∈ Set.range (inclusion p (residueExtension p n))) ∧
      ∀ w, (sextic ((upper a b ρ)^6) ((lower a b ρ)^6)).IsRoot w →
        w ∈ Set.range (inclusion p (residueExtension p n)) := by
  let ι : ℤ_[p] →+* WittRing p :=
    (WittVector.map (algebraMap (ZMod p) (Residues p))).comp (WittVector.equiv p).symm.toRingHom
  let : CharZero (WittRing p) := charZero_of_injective_ringHom (f := ι)
    ((WittVector.map_injective _ (algebraMap (ZMod p) (Residues p)).injective).comp
      (WittVector.equiv p).symm.injective)
  let U := (upper a b ρ)^6
  let V := (lower a b ρ)^6
  let P : (WittRing p)[X] := (X^2+2)*(X^2+3)*sextic U V*sextic V U
  obtain ⟨hu, hv⟩ := coordinates_nonzero a b hb hρ
  have d₁ := sextic_degree U (pow_ne_zero 6 hv)
  have d₂ := sextic_degree V (pow_ne_zero 6 hu)
  have hz : ((X^2+2)*(X^2+3) : (WittRing p)[X]) ≠ 0 := by
    have hd : ((X^2+2)*(X^2+3) : (WittRing p)[X]).natDegree = 4 := by compute_degree!
    intro h; simp [h] at hd
  have hp : P ≠ 0 := mul_ne_zero (mul_ne_zero hz (fun h => by simp [V, h] at d₁))
    (fun h => by simp [U, h] at d₂)
  have fρ : frob p ρ = ρ ∨ frob p ρ = -ρ := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [← map_pow, hρ, map_neg, map_ofNat]
  have hf : P.map (frob p) = P := by
    simp only [P, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, map_X,
      Polynomial.map_ofNat, sextic_map, U, V, upper, lower, map_pow, map_add, map_sub,
      map_mul, map_intCast]
    rcases fρ with h|h
    · rw [h]
    · rw [h]; simp only [neg_mul, ← sub_eq_add_neg, sub_neg_eq_add]
      ring
  obtain ⟨n, hn, allroots⟩ := finite_ring_for_roots p P hp hf
  refine ⟨n, hn, allroots ρ ?_, fun z hz => allroots z ?_, fun w hw => allroots w ?_⟩
  · simp [P, IsRoot, hρ]
  · simp [P, IsRoot, hz]
  · have hw' : (sextic U V).eval w = 0 := hw
    simp [P, IsRoot, hw']

end Descent

section FiniteWitt

open scoped Pointwise
variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Finite k] [CharP k p]

def fromPadics : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (by simp) k)).comp (WittVector.equiv p).symm.toRingHom

local instance : Algebra ℤ_[p] (WittVector p k) := (fromPadics p k).toAlgebra

private theorem maximal_map : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (WittVector p k)) =
    maximalIdeal (WittVector p k) := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  exact (show Irreducible (p : WittVector p k) from WittVector.irreducible p).maximalIdeal_eq.symm

private theorem congruence {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q : R) (m : ℕ) (x y : M) :
    x ≡ y [SMOD ((Ideal.span {q})^m • ⊤ : Submodule R M)] ↔
    ∃ z : M, q^m • z = x-y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- Coordinatewise completeness for a finite free source, in the form
needed to lift residue generators to integral generators. -/
private theorem pi_precomplete (ι : Type*) :
    IsPrecomplete (maximalIdeal ℤ_[p]) (ι → ℤ_[p]) := by
  constructor
  intro t ht
  have each (i : ι) : ∃ z : ℤ_[p], ∀ n,
      t n i ≡ z [SMOD ((maximalIdeal ℤ_[p])^n • ⊤ : Submodule ℤ_[p] ℤ_[p])] := by
    apply IsPrecomplete.prec' (I := maximalIdeal ℤ_[p]) (fun n => t n i)
    intro m n hmn
    have h := ht hmn
    rw [PadicInt.maximalIdeal_eq_span_p, congruence] at h ⊢
    obtain ⟨z, hz⟩ := h
    exact ⟨z i, congrFun hz i⟩
  choose z hz using each
  refine ⟨z, fun n => ?_⟩
  rw [PadicInt.maximalIdeal_eq_span_p, congruence]
  have lifts (i : ι) : ∃ a : ℤ_[p], (p : ℤ_[p])^n • a = t n i-z i := by
    have h := hz i n
    rwa [PadicInt.maximalIdeal_eq_span_p, congruence] at h
  choose a ha using lifts
  exact ⟨a, funext ha⟩

/-- For every finite residue field the Witt ring is finite over the actual
`p`-adic integers. Modulo `p` the Teichmüller representatives span; completeness
of the free source and separatedness of the target lift the spanning property. -/
theorem finite_witt : Module.Finite ℤ_[p] (WittVector p k) := by
  classical
  let := Fintype.ofFinite k
  let A := ℤ_[p]
  let W := WittVector p k
  let I := maximalIdeal A
  let t : k → W := WittVector.teichmuller p
  let f : (k → A) →ₗ[A] W := Fintype.linearCombination A t
  let : IsPrecomplete I (k → A) := pi_precomplete p k
  have maxW : maximalIdeal W = Ideal.span {(p : W)} :=
    (show Irreducible (p : W) from WittVector.irreducible p).maximalIdeal_eq
  let : IsHausdorff I W := by
    apply (IsHausdorff.map_algebraMap_iff (I := maximalIdeal ℤ_[p]) (S := WittVector p k)
      (M := WittVector p k)).mp
    change IsHausdorff ((maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] W)) W
    rw [maximal_map, maxW]
    infer_instance
  apply Module.Finite.of_surjective f
  apply surjective_of_mkQ_comp_surjective (I := I)
  intro z
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A W)) z
  let a := w.coeff 0
  refine ⟨Pi.single a 1, ?_⟩
  change (I • (⊤ : Submodule A W)).mkQ (Fintype.linearCombination A t (Pi.single a 1)) = _
  rw [Fintype.linearCombination_apply_single, one_smul, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq]
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, maximal_map, maxW, ← WittVector.ker_constantCoeff]
  change WittVector.constantCoeff (t a-w) = 0
  rw [map_sub, sub_eq_zero]
  exact WittVector.teichmuller_coeff_zero p _

private local instance : Module.Finite ℤ_[p] (WittVector p k) := finite_witt p k

private local instance : IsLocalHom (algebraMap ℤ_[p] (WittVector p k)) :=
  ((IsLocalRing.local_hom_TFAE _).out 1 3 rfl rfl).mpr (maximal_map p k).le

private def residueEquiv : ResidueField (WittVector p k) ≃+* k :=
  (Ideal.quotEquivOfEq (show maximalIdeal (WittVector p k) = Ideal.span {(p : WittVector p k)}
    from (WittVector.irreducible p).maximalIdeal_eq)).trans WittVector.quotientPEquiv

/-- Finiteness and formal unramifiedness together with the exact local
ramification index of this integral extension. -/
theorem witt_unramified : Module.Finite ℤ_[p] (WittVector p k) ∧
    Algebra.FormallyUnramified ℤ_[p] (WittVector p k) ∧
    (maximalIdeal (WittVector p k)).ramificationIdx ℤ_[p] = 1 := by
  let : Finite (ResidueField (WittVector p k)) := Finite.of_injective _ (residueEquiv p k).injective
  let : Algebra.FormallyUnramified ℤ_[p] (WittVector p k) :=
    Algebra.FormallyUnramified.of_map_maximalIdeal (maximal_map p k)
  exact ⟨inferInstance, inferInstance, Ideal.ramificationIdx_eq_one _ _⟩

theorem witt_finite_etale : Module.Finite ℤ_[p] (WittVector p k) ∧ Algebra.Etale ℤ_[p] (WittVector p k) := by
  have inj : Function.Injective (fromPadics p k) :=
    (WittVector.map_injective _ (ZMod.castHom (by simp) k).injective).comp (WittVector.equiv p).symm.injective
  let : Module.IsTorsionFree ℤ_[p] (WittVector p k) := Module.isTorsionFree_iff_algebraMap_injective.mpr inj
  let : Algebra.FormallyUnramified ℤ_[p] (WittVector p k) := (witt_unramified p k).2.1
  let : Algebra.FinitePresentation ℤ_[p] (WittVector p k) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, .of_formallyUnramified_of_flat⟩

omit [Finite k] in
private theorem toFraction_injective : Function.Injective
    (algebraMap ℤ_[p] (FractionRing (WittVector p k))) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] (WittVector p k) (FractionRing (WittVector p k))]
  exact (IsFractionRing.injective (WittVector p k) _).comp
    ((WittVector.map_injective _ (ZMod.castHom (by simp) k).injective).comp (WittVector.equiv p).symm.injective)

@[instance_reducible] def wittFractionAlgebra : Algebra ℚ_[p] (FractionRing (WittVector p k)) :=
  (IsFractionRing.lift (toFraction_injective p k)).toAlgebra

local instance : Algebra ℚ_[p] (FractionRing (WittVector p k)) := wittFractionAlgebra p k
private local instance : IsScalarTower ℤ_[p] ℚ_[p] (FractionRing (WittVector p k)) :=
  IsScalarTower.of_algebraMap_eq (R := ℤ_[p]) (S := ℚ_[p]) (A := FractionRing (WittVector p k))
    fun x => (IsFractionRing.lift_algebraMap (toFraction_injective p k) x).symm

/-- The fraction field is a finite extension of the actual `p`-adic field.
Its Witt DVR is the integral closure of the `p`-adic integers there. -/
theorem witt_fraction_unramified :
    FiniteDimensional ℚ_[p] (FractionRing (WittVector p k)) ∧
    IsIntegralClosure (WittVector p k) ℤ_[p] (FractionRing (WittVector p k)) ∧
    (maximalIdeal (WittVector p k)).ramificationIdx ℤ_[p] = 1 := by
  have inj : Function.Injective (fromPadics p k) :=
    (WittVector.map_injective _ (ZMod.castHom (by simp) k).injective).comp (WittVector.equiv p).symm.injective
  let : Module.IsTorsionFree ℤ_[p] (WittVector p k) := Module.isTorsionFree_iff_algebraMap_injective.mpr inj
  refine ⟨Module.finite_of_finrank_pos ?_, IsIntegralClosure.of_isIntegrallyClosedIn, (witt_unramified p k).2.2⟩
  rw [IsFractionRing.finrank_eq ℤ_[p] ℚ_[p] (WittVector p k) (FractionRing (WittVector p k))]
  exact Module.finrank_pos

/-- The same integral splitting extension is finite étale over the integers
of every intermediate coefficient field, in particular over the integers of
`ℚₚ(ρ)`. The embedding commutes with both given maps to the fraction field. -/
theorem relative_finite_etale (K : IntermediateField ℚ_[p] (FractionRing (WittVector p k))) :
    let S := WittVector p k
    let L := FractionRing S
    let O := integralClosure ℤ_[p] K
    ∃ ψ : O →ₐ[ℤ_[p]] S,
      (∀ x : O, algebraMap S L (ψ x)=algebraMap K L (x:K)) ∧
      letI := ψ.toRingHom.toAlgebra
      Module.Finite O S ∧ Algebra.Etale O S ∧
        (maximalIdeal S).ramificationIdx O = 1 ∧ ((maximalIdeal S).under O).ramificationIdx ℤ_[p] = 1 := by
  let S := WittVector p k
  let L := FractionRing S
  let O := integralClosure ℤ_[p] K
  have prop := witt_fraction_unramified p k
  let : FiniteDimensional ℚ_[p] L := prop.1
  let : IsIntegralClosure S ℤ_[p] L := prop.2.1
  let : IsDedekindDomain O := integralClosure.isDedekindDomain ℤ_[p] ℚ_[p] K
  let θ : K →ₐ[ℤ_[p]] L := K.val.restrictScalars ℤ_[p]
  let eqv := IsIntegralClosure.equiv ℤ_[p] (integralClosure ℤ_[p] L) L S
  let ψ : O →ₐ[ℤ_[p]] S := eqv.toAlgHom.comp θ.mapIntegralClosure
  have hψ (x : O) : algebraMap S L (ψ x) = algebraMap K L (x:K) :=
    IsIntegralClosure.algebraMap_equiv ℤ_[p] (integralClosure ℤ_[p] L) L S (θ.mapIntegralClosure x)
  refine ⟨ψ, hψ, ?_⟩
  let := ψ.toRingHom.toAlgebra
  let : IsScalarTower ℤ_[p] O S := IsScalarTower.of_algebraMap_eq (R := ℤ_[p]) (S := O) (A := S)
    fun x => (ψ.commutes x).symm
  have inj : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    apply (algebraMap K L).injective
    exact (hψ x).symm.trans ((congrArg (algebraMap S L) h).trans (hψ y))
  let : Module.IsTorsionFree O S := Module.isTorsionFree_iff_algebraMap_injective.mpr inj
  let : Module.Finite O S := Module.Finite.of_restrictScalars_finite ℤ_[p] O S
  let : Algebra.FormallyUnramified ℤ_[p] S := (witt_unramified p k).2.1
  let : Algebra.FormallyUnramified O S := .of_restrictScalars ℤ_[p] O S
  let : Algebra.FinitePresentation O S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale O S := .of_formallyUnramified_of_flat
  have dv := Ideal.ramificationIdx_below_dvd (R := ℤ_[p]) ((maximalIdeal S).under O) (maximalIdeal S)
  rw [(witt_unramified p k).2.2] at dv
  exact ⟨inferInstance, inferInstance, Ideal.ramificationIdx_eq_one _ _, Nat.dvd_one.mp dv⟩

end FiniteWitt

section Models

variable (p : ℕ) [Fact p.Prime] (a b e : ℤ) (ρ : WittRing p)

/-- A finite subfield of the algebraic residue closure, a lift of the specified
square root and a split model of the actual twisted sextic in its Witt ring. -/
structure FiniteSplitting where
  field : Subfield (Residues p)
  finite : Finite field
  rho : WittVector p field
  inclusion_rho : inclusion p field rho = ρ
  radical : ∀ z : WittRing p, z^2 = -2 → z ∈ Set.range (inclusion p field)
  splits : (twisted a b e rho).Splits

theorem finite_twisted_splitting (hb : b ≠ 0) (hρ : ρ^2 = -3)
    (hs : (sextic ((upper a b ρ)^6) ((lower a b ρ)^6)).Splits) :
    Nonempty (FiniteSplitting p a b e ρ) := by
  obtain ⟨n, hn, ⟨r, hr⟩, radical, roots⟩ := finite_ring_for_family p a b hb hρ
  let F := residueExtension p n
  let ι := inclusion p F
  let g := sextic ((upper a b r)^6) ((lower a b r)^6)
  have hm : g.map ι = sextic ((upper a b ρ)^6) ((lower a b ρ)^6) := by
    rw [sextic_map]
    simp only [upper, lower, map_pow, map_add, map_intCast, map_mul, map_sub, show ι r = ρ from hr]
  have small : g.Splits := by
    have hmap : (g.map ι).Splits := hm ▸ hs
    apply hmap.of_splits_map_of_injective (inclusion_injective p F)
    rw [hm]
    exact fun w hw => roots w (isRoot_of_mem_roots hw)
  exact ⟨⟨F, residueExtension_finite p hn, r, hr, radical, (Splits.C _).mul small⟩⟩

end Models

section Clusters

open ZInQBlueprint.HenselTriples
abbrev Index := Fin 2 × Fin 3
abbrev Cluster := Finset Index

/-- The roots in row `i` have a positive mutual depth precisely for `i ∈ A`.
All differences in an active row are `c` times units. All remaining
differences between distinct points are units. -/
structure Configuration {R : Type*} [CommRing R] (f : R[X]) (A : Finset (Fin 2)) (c : R) where
  point : Index → R
  root : ∀ i, f.IsRoot (point i)
  deep : ∀ i j : Index, i ≠ j → i.1 = j.1 → i.1 ∈ A →
    ∃ z : Rˣ, point i-point j = c*(z:R)
  shallow : ∀ i j : Index, i ≠ j → ¬(i.1 = j.1 ∧ i.1 ∈ A) → IsUnit (point i-point j)

theorem configuration_two {R : Type*} [CommRing R] [IsLocalRing R] {f : R[X]} {c : R}
    {a : Fin 2 → R} {ξ : Fin 2 → Fin 3 → ResidueField R} (T : TwoTriples f a c ξ) :
    Nonempty (Configuration f Finset.univ c) := by
  refine ⟨⟨fun i => a i.1+c*T.y i.1 i.2, fun i => T.root i.1 i.2, ?_, ?_⟩⟩
  · rintro ⟨i,s⟩ ⟨j,t⟩ h hrow _
    change i = j at hrow
    subst j
    exact T.within i s t (fun he => h (Prod.ext rfl he))
  · rintro ⟨i,s⟩ ⟨j,t⟩ _ h
    exact T.across i j (fun he => h ⟨he, Finset.mem_univ _⟩) s t

theorem configuration_one {R : Type*} [CommRing R] [IsLocalRing R] {u V : R}
    (T : ZeroFibreRoots u V) (hu : residue R u = 0) :
    Nonempty (Configuration (sextic (u^6) V) {0} (u^2)) := by
  obtain ⟨inner, outer, across⟩ := zero_contact_distances T hu
  let x : Index → R := fun i => if i.1=0 then u^2*T.inner i.2 else T.outer i.2
  refine ⟨⟨x, ?_, ?_, ?_⟩⟩
  · rintro ⟨i,j⟩
    fin_cases i
    · exact T.innerRoot j
    · exact T.outerRoot j
  · rintro ⟨i,s⟩ ⟨j,t⟩ h hrow hactive
    change i=j at hrow
    have hi : i=0 := Finset.mem_singleton.mp hactive
    subst i; subst j
    exact inner s t (fun he => h (Prod.ext rfl he))
  · rintro ⟨i,s⟩ ⟨j,t⟩ h hrow
    fin_cases i <;> fin_cases j
    · exact False.elim (hrow ⟨rfl, Finset.mem_singleton_self _⟩)
    · exact across s t
    · change IsUnit (T.outer s-u^2*T.inner t)
      simpa only [neg_sub] using (across t s).neg
    · exact outer s t (fun he => h (Prod.ext rfl he))

private theorem unit_value {R K Γ : Type*} [CommRing R] [CommRing K]
    [LinearOrderedAddCommMonoidWithTop Γ] (ι : R →+* K) (v : AddValuation K Γ)
    (hunit : ∀ u : Rˣ, v (ι (u:R))=0) {x : R} (hx : IsUnit x) : v (ι x) = 0 := by
  obtain ⟨u,rfl⟩ := hx
  exact hunit u

def distances {Γ : Type*} [Zero Γ] [Top Γ] (A : Finset (Fin 2)) (m : Γ) (i j : Index) : Γ :=
  if i=j then ⊤ else if i.1=j.1 ∧ i.1∈A then m else 0

theorem pairwise_valuations {R K Γ : Type*} [CommRing R] [CommRing K]
    [LinearOrderedAddCommMonoidWithTop Γ] {f : R[X]} {A : Finset (Fin 2)} {c : R}
    (T : Configuration f A c) (ι : R →+* K) (v : AddValuation K Γ)
    (units : ∀ u : Rˣ, v (ι (u:R))=0) (i j : Index) :
    v (ι (T.point i)-ι (T.point j)) = distances A (v (ι c)) i j := by
  by_cases he : i=j
  · subst j; simp [distances]
  · rw [← map_sub]
    by_cases h : i.1=j.1 ∧ i.1∈A
    · obtain ⟨z, hz⟩ := T.deep i j he h.1 h.2
      rw [hz, map_mul, v.map_mul, units, add_zero]
      rw [distances, ite_eq_right he, ite_eq_left h]
    · simpa [distances, he, h] using unit_value ι v units (T.shallow i j he h)

private theorem recenter {K Γ : Type*} [CommRing K] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation K Γ) (x b z : K) (t : Γ) (hb : t ≤ v (b-z)) :
    t ≤ v (x-z) ↔ t ≤ v (x-b) := by
  constructor
  · intro h
    have h' : t ≤ v (z-b) := by rwa [v.map_sub_swap]
    simpa only [sub_add_sub_cancel] using v.map_le_add h h'
  · intro h
    simpa only [sub_add_sub_cancel] using v.map_le_add h hb

/-- All nonempty geometric discs, also for valuations with fractional radii.
The same calculation covers the smooth and both contact configurations. -/
theorem geometric_disc {R K Γ : Type*} [CommRing R] [CommRing K] [LinearOrderedAddCommMonoidWithTop Γ]
    {f : R[X]} {A : Finset (Fin 2)} {c : R} (T : Configuration f A c)
    (ι : R →+* K) (v : AddValuation K Γ) (units : ∀ u : Rˣ, v (ι (u:R))=0)
    (hpos : 0 ≤ v (ι c)) (z : K) (t : Γ) (b : Index) (hb : t ≤ v (ι (T.point b)-z)) :
    {i | t ≤ v (ι (T.point i)-z)} = if t ≤ 0 then Set.univ else
      if t ≤ v (ι c) ∧ b.1∈A then {i : Index | i.1=b.1} else {b} := by
  classical
  ext i
  change t ≤ v (ι (T.point i)-z) ↔ _
  rw [recenter v _ _ _ _ hb, pairwise_valuations T ι v units, distances]
  by_cases he : i=b
  · subst i; split_ifs <;> simp_all
  · rw [ite_eq_right he]
    by_cases ht : t ≤ 0
    · rw [ite_eq_left ht]
      simp only [Set.mem_univ, iff_true]
      split_ifs
      · exact ht.trans hpos
      · exact ht
    · rw [ite_eq_right ht]
      by_cases hr : i.1=b.1
      · by_cases ha : b.1 ∈ A <;> by_cases hm : t ≤ v (ι c) <;> simp [hr, ha, hm, he, ht]
      · by_cases h : t ≤ v (ι c) ∧ b.1∈A <;> simp [h, hr, he, ht]

def row (i : Fin 2) : Cluster := Finset.univ.filter fun b => b.1=i
def tree (A : Finset (Fin 2)) : Finset Cluster :=
  {Finset.univ} ∪ A.image row ∪ Finset.univ.image (fun i : Index => {i})

theorem mem_tree : ∀ (A : Finset (Fin 2)) (s : Cluster), s∈tree A ↔
    s=Finset.univ ∨ (∃ i∈A, s=row i) ∨ ∃ b : Index, s={b} := by decide

theorem coe_row (i : Fin 2) : (row i : Set Index) = {b | b.1=i} := by ext; simp [row]

/-- For prolongations of the normalized valuation the displayed tree is
exactly the collection of nonempty intersections with geometric closed discs. -/
theorem geometric_iff {R K Γ : Type*} [CommRing R] [CommRing K] [LinearOrderedAddCommMonoidWithTop Γ]
    {f : R[X]} {A : Finset (Fin 2)} {c : R} (T : Configuration f A c)
    (ι : R →+* K) (v : AddValuation K Γ) (units : ∀ u : Rˣ, v (ι (u:R))=0)
    (hpos : 0 ≤ v (ι c)) (hactive : A.Nonempty → 0 < v (ι c))
    (hmore : ∃ t, v (ι c)<t ∧ t<⊤) (s : Cluster) :
    (s.Nonempty ∧ ∃ z t, t<⊤ ∧ (s:Set Index)={i | t≤v (ι (T.point i)-z)}) ↔ s∈tree A := by
  obtain ⟨t₁,h₁,h₂⟩ := hmore
  have hit (b : Index) (t : Γ) : t ≤ v (ι (T.point b)-ι (T.point b)) := by simp
  rw [mem_tree]
  constructor
  · rintro ⟨⟨b,hb⟩,z,t,_,hs⟩
    have hd : b ∈ {i | t≤v (ι (T.point i)-z)} := by rw [← hs]; exact hb
    rw [geometric_disc T ι v units hpos z t b hd] at hs
    split_ifs at hs with ht hk
    · exact Or.inl (Finset.coe_injective (hs.trans Finset.coe_univ.symm))
    · exact Or.inr (Or.inl ⟨b.1, hk.2, Finset.coe_injective (hs.trans (coe_row _).symm)⟩)
    · exact Or.inr (Or.inr ⟨b, Finset.coe_injective (by simpa only [Finset.coe_singleton] using hs)⟩)
  · rintro (rfl | ⟨i,hi,rfl⟩ | ⟨b,rfl⟩)
    · refine ⟨Finset.univ_nonempty, ι (T.point (0,0)), 0, hpos.trans_lt (h₁.trans h₂), ?_⟩
      rw [geometric_disc T ι v units hpos _ _ _ (hit (0,0) 0)]; simp
    · refine ⟨⟨(i,0), by simp [row]⟩, ι (T.point (i,0)), v (ι c), h₁.trans h₂, ?_⟩
      rw [geometric_disc T ι v units hpos _ _ _ (hit (i,0) _)]
      simp [(hactive ⟨i,hi⟩).not_ge, hi, coe_row]
    · refine ⟨Finset.singleton_nonempty b, ι (T.point b), t₁, h₂, ?_⟩
      rw [geometric_disc T ι v units hpos _ _ _ (hit b t₁)]
      simp [(hpos.trans_lt h₁).not_ge, h₁.not_ge]
def children (A : Finset (Fin 2)) (s : Cluster) : Finset Cluster :=
  (tree A).filter fun t => t ⊂ s ∧ ∀ u ∈ tree A, ¬(t ⊂ u ∧ u ⊂ s)
def principal (A : Finset (Fin 2)) (s : Cluster) : Prop :=
  s ∈ tree A ∧ 3 ≤ s.card ∧ ¬(s=Finset.univ ∧ Even s.card ∧ (children A s).card=2) ∧
    ∀ t ∈ children A s, t.card ≠ 4

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
theorem principal_iff (A : Finset (Fin 2)) (s : Cluster) :
    principal A s ↔ (s=Finset.univ ∧ A≠Finset.univ) ∨ ∃ i ∈ A, s=row i := by
  have h : ∀ B : Finset (Fin 2), ∀ t ∈ tree B,
      (3 ≤ t.card ∧ ¬(t=Finset.univ ∧ Even t.card ∧ (children B t).card=2) ∧
        ∀ v ∈ children B t, v.card ≠ 4) ↔
      (t=Finset.univ ∧ B≠Finset.univ) ∨ ∃ i ∈ B, t=row i := by decide
  constructor
  · rintro ⟨ht, ht'⟩; exact (h A s ht).mp ht'
  · intro hs
    have ht : s ∈ tree A := by
      rcases hs with ⟨rfl,_⟩ | ⟨i,hi,rfl⟩
      · simp [tree]
      · simp [tree, Finset.mem_image_of_mem row hi]
    exact ⟨ht, (h A s ht).mpr hs⟩

theorem proper_odd : ∀ (A : Finset (Fin 2)), ∀ s ∈ tree A, s ≠ Finset.univ → Odd s.card := by decide

def joinRoot (A : Finset (Fin 2)) (s : Cluster) (r : Index) : Cluster :=
  ((tree A).filter fun t => s ⊆ t ∧ r∈t).inf id

theorem join_row : ∀ (A : Finset (Fin 2)) (i : Fin 2), i∈A → ∀ r : Index,
    joinRoot A (row i) r = if r.1=i then row i else Finset.univ := by decide
theorem join_top : ∀ (A : Finset (Fin 2)) (r : Index), joinRoot A Finset.univ r = Finset.univ := by decide

def depth (dist : Index → Index → ℕ∞) (s : Cluster) : ℕ∞ :=
  (s ×ˢ s).inf fun ij => dist ij.1 ij.2

theorem row_depth (A : Finset (Fin 2)) (m : ℕ) {i : Fin 2} (hi : i∈A) :
    depth (distances A (m:ℕ∞)) (row i) = m := by
  apply le_antisymm
  · have hh := Finset.inf_le (f := fun xy : Index × Index => distances A (m:ℕ∞) xy.1 xy.2)
        (show ((i,0),(i,1)) ∈ row i ×ˢ row i by simp [row])
    simpa [depth, distances, hi] using hh
  · apply Finset.le_inf
    intro xy h
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp h
    simp [row] at hx hy
    by_cases hxy : xy.1=xy.2 <;> simp [distances, hx, hy, hxy, hi]

theorem top_depth (A : Finset (Fin 2)) (m : ℕ) :
    depth (distances A (m:ℕ∞)) Finset.univ = 0 := by
  apply le_antisymm _ bot_le
  have hh := Finset.inf_le (f := fun xy : Index × Index => distances A (m:ℕ∞) xy.1 xy.2)
    (show (((0,0):Index),((1,0):Index)) ∈ (Finset.univ:Cluster) ×ˢ Finset.univ by simp)
  simpa [depth, distances] using hh

/-- The DDMM sum of the order of the leading coefficient and the six depths
of the joins with the individual roots. -/
def nu (lead : ℤ) (A : Finset (Fin 2)) (dist : Index → Index → ℕ∞) (s : Cluster) : ℤ :=
  lead + ∑ r : Index, ((depth dist (joinRoot A s r)).toNat : ℤ)

theorem nu_row (lead : ℤ) (A : Finset (Fin 2)) (m : ℕ) {i : Fin 2} (hi : i∈A) :
    nu lead A (distances A (m:ℕ∞)) (row i) = lead+3*m := by
  have eqn (r : Index) : ((depth (distances A (m:ℕ∞)) (joinRoot A (row i) r)).toNat : ℤ) =
      if r.1=i then (m:ℤ) else 0 := by
    rw [join_row A i hi r]
    split_ifs <;> simp [row_depth A m hi, top_depth]
  simp only [nu, eqn]
  fin_cases i <;> simp [Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring

theorem nu_top (lead : ℤ) (A : Finset (Fin 2)) (m : ℕ) :
    nu lead A (distances A (m:ℕ∞)) Finset.univ = lead := by simp [nu, join_top, top_depth]

theorem even_nu (r : ℕ) {lead : ℤ} (he : Even (lead+(r:ℤ))) {s : Cluster}
    (hs : principal Finset.univ s) : Even (nu lead Finset.univ (distances Finset.univ (r:ℕ∞)) s) := by
  rcases (principal_iff _ _).mp hs with ⟨_,h⟩ | ⟨i,hi,rfl⟩
  · exact (h rfl).elim
  · rw [nu_row _ _ _ hi, Int.even_iff]
    rw [Int.even_iff] at he
    omega

theorem zero_nu (r : ℕ) {s : Cluster} (hs : principal {0} s) :
    Even (nu 0 {0} (distances {0} ((2*r:ℕ):ℕ∞)) s) := by
  rcases (principal_iff _ _).mp hs with ⟨rfl,_⟩ | ⟨i,hi,rfl⟩
  · rw [nu_top]; exact ⟨0, rfl⟩
  · rw [nu_row _ _ _ hi, Int.even_iff]
    push_cast
    omega

end Clusters

section Arithmetic

open IsDiscreteValuationRing ZInQBlueprint.HenselTriples

theorem sextic_leading {R : Type*} [CommRing R] [IsDomain R] (U : R) {V : R} (hV : V ≠ 0) :
    (sextic U V).leadingCoeff = -V := by
  have ex : sextic U V = C (-V)*X^6+C (-6*V)*X^5+C (-6*V)*X^4+
      C (8*U+8*V)*X^3+C (12*U)*X^2+C (-24*U)*X+C (8*U) := by
    simp [sextic, quartic, quadratic, map_ofNat]
    ring
  rw [← coeff_natDegree, sextic_degree U hV, ex]
  have top (a b c d e f g : R) :
      (C a*X^6+C b*X^5+C c*X^4+C d*X^3+C e*X^2+C f*X+C g).coeff 6 = a := by
    simp [coeff_add, coeff_C_mul, coeff_X_pow]
  exact top ..

def multiplyConfiguration {R : Type*} [CommRing R] {f : R[X]} {A : Finset (Fin 2)} {c : R}
    (s : R) (T : Configuration f A c) : Configuration (C s*f) A c where
  point := T.point
  root i := by simp [IsRoot, show f.eval (T.point i) = 0 from T.root i]
  deep := T.deep
  shallow := T.shallow

def changeRadius {R : Type*} [CommRing R] {f : R[X]} {A : Finset (Fin 2)} {c d : R}
    (T : Configuration f A c) (e : Rˣ) (h : c=d*(e:R)) : Configuration f A d where
  point := T.point
  root := T.root
  deep i j ne same active := by
    obtain ⟨u,hu⟩ := T.deep i j ne same active
    exact ⟨e*u, by rw [hu, h, Units.val_mul, mul_assoc]⟩
  shallow := T.shallow

theorem configuration_exhausts {R : Type*} [CommRing R] [IsDomain R] {f : R[X]} {A : Finset (Fin 2)}
    {c : R} (T : Configuration f A c) (hc : c ≠ 0) (hd : f.natDegree = 6) :
    f.roots.Nodup ∧ f.Splits ∧ ∀ w, f.IsRoot w ↔ ∃ i, T.point i=w := by
  classical
  have hf : f ≠ 0 := by intro h; simp [h] at hd
  have inj : Function.Injective T.point := by
    intro i j h
    by_contra he
    by_cases hrow : i.1=j.1 ∧ i.1∈A
    · obtain ⟨u, hu⟩ := T.deep i j he hrow.1 hrow.2
      exact (mul_ne_zero hc u.ne_zero) (hu.symm.trans (sub_eq_zero.mpr h))
    · exact (T.shallow i j he hrow).ne_zero (sub_eq_zero.mpr h)
  have sub : Finset.univ.image T.point ⊆ f.roots.toFinset := by
    rintro _ h
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
    exact Multiset.mem_toFinset.mpr ((mem_roots hf).mpr (T.root i))
  have card : (Finset.univ.image T.point).card = 6 := by simp [Finset.card_image_of_injective _ inj]
  have h₁ := Finset.card_le_card sub
  rw [card] at h₁
  have h₂ := Multiset.toFinset_card_le f.roots
  have h₃ := card_roots' f
  have equality := Finset.eq_of_subset_of_card_le sub (show _ by omega)
  refine ⟨Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega), splits_iff_card_roots.mpr (by omega), ?_⟩
  intro w
  rw [← mem_roots hf, ← Multiset.mem_toFinset, ← equality, Finset.mem_image]
  simp

/-- The same six labels give all geometric roots in every field containing
the splitting DVR. The fraction-field sextic is separable, including at the
parameters whose integral reduction has multiple roots. -/
theorem geometric_roots {R K : Type*} [CommRing R] [IsDomain R] [Field K] {f : R[X]}
    {A : Finset (Fin 2)} {c : R} (T : Configuration f A c) (hc : c ≠ 0) (hd : f.natDegree=6)
    (ι : R →+* K) (hi : Function.Injective ι) :
    (f.map ι).natDegree=6 ∧ (f.map ι).Separable ∧ (f.map ι).Splits ∧
      ∀ w, (f.map ι).IsRoot w ↔ ∃ i, ι (T.point i)=w := by
  obtain ⟨nd, hs, full⟩ := configuration_exhausts T hc hd
  have d := (natDegree_map_eq_of_injective hi f).trans hd
  have hz : f ≠ 0 := by intro h; simp [h] at hd
  have hn : f.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hi).mpr hz
  have split := hs.map ι
  have hr := hs.roots_map_of_injective hi
  refine ⟨d, (nodup_roots_iff_of_splits hn split).mp (hr ▸ Multiset.Nodup.map hi nd), split, ?_⟩
  intro w
  rw [← mem_roots hn, hr, Multiset.mem_map]
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨i,rfl⟩ := (full x).mp (isRoot_of_mem_roots hx)
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨T.point i, (mem_roots hz).mpr (T.root i), rfl⟩

theorem smooth_configuration {R : Type*} [CommRing R] [IsLocalRing R] [HenselianRing R (maximalIdeal R)]
    [IsAlgClosed (ResidueField R)] {f : R[X]} (hsep : (f.map (residue R)).Separable)
    (hd : (f.map (residue R)).natDegree = 6) : Nonempty (Configuration f ∅ 1) := by
  classical
  let g := f.map (residue R)
  let S := g.roots.toFinset
  have card : Fintype.card S=6 := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree]
    exact hd
  let eqv : Index ≃ S := Fintype.equivOfCardEq (by simpa using card.symm)
  have root (i : Index) : g.IsRoot (eqv i).val := isRoot_of_mem_roots (Multiset.mem_toFinset.mp (eqv i).property)
  have lift (i : Index) : ∃ x : R, f.IsRoot x ∧ residue R x=(eqv i).val := by
    apply liftSimple f
    · rw [eval₂_eq_eval_map]; exact root i
    · rw [eval₂_eq_eval_map, ← derivative_map]
      exact hsep.eval₂_derivative_ne_zero (RingHom.id _) (root i)
  choose point hp hr using lift
  refine ⟨⟨point, hp, fun _ _ _ _ h => (Finset.notMem_empty _ h).elim, ?_⟩⟩
  intro i j hij _
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [map_sub, hr, hr]
  exact sub_ne_zero.mpr (fun h => hij (eqv.injective (Subtype.ext h)))

variable (p : ℕ) [Fact p.Prime]
local notation "W" => WittRing p

private def strictResidue : ResidueField W ≃+* Residues p :=
  (Ideal.quotEquivOfEq (show IsLocalRing.maximalIdeal W = Ideal.span {(p : W)} from
    (WittVector.irreducible p).maximalIdeal_eq)).trans WittVector.quotientPEquiv

private local instance : IsAlgClosed (ResidueField W) := IsAlgClosed.of_ringEquiv _ _ (strictResidue p).symm
private local instance : CharP (ResidueField W) p :=
  charP_of_injective_ringHom (f := (strictResidue p).symm.toRingHom) (strictResidue p).symm.injective p
private local instance : HenselianRing W (IsLocalRing.maximalIdeal W) := by
  rw [(show Irreducible (p:W) from WittVector.irreducible p).maximalIdeal_eq]
  infer_instance
private local instance : CharZero W :=
  charZero_of_injective_ringHom (f := fromPadics p (Residues p))
    ((WittVector.map_injective _ (ZMod.castHom (by simp) (Residues p)).injective).comp
      (WittVector.equiv p).symm.injective)

private theorem actual_leading (a b e : ℤ) {ρ : W} (hv : IsUnit (lower a b ρ)) :
    (twisted a b e ρ).leadingCoeff = (2*(e:W)) * -(lower a b ρ)^6 := by
  rw [twisted, leadingCoeff_mul, leadingCoeff_C, sextic_leading _ (pow_ne_zero _ hv.ne_zero)]

private theorem lead_order (hp : 3 < p) (a b e : ℤ) {ρ : W} (hv : IsUnit (lower a b ρ)) :
    addVal W (twisted a b e ρ).leadingCoeff = addVal W (e:W) := by
  have tw : IsUnit (2:W) := (residue_ne_zero_iff_isUnit _).mp (by
    simpa only [map_ofNat] using (residue_characteristic (k := ResidueField W) p hp).1)
  rw [actual_leading _ _ _ _ hv, addVal_mul, addVal_mul, addVal_eq_zero_iff.mpr tw,
    addVal_eq_zero_iff.mpr (hv.pow 6).neg, zero_add, add_zero]

/-- The split model, root configuration and principal-cluster valuation test
for a sextic over a discretely valued ring. -/
structure ClusterData {R : Type*} [CommRing R] (model : Type*) (f : R[X])
    (A : Finset (Fin 2)) (radius : R) (ord : R → ℕ∞) where
  finiteModel : model
  degree : f.natDegree = 6
  roots : Configuration f A radius
  exhaustive : ∀ w, f.IsRoot w ↔ ∃ i, roots.point i=w
  odd : ∀ s ∈ tree A, s ≠ Finset.univ → Odd s.card
  parity : ∀ s, principal A s → Even (nu ((ord f.leadingCoeff).toNat:ℤ) A
    (fun i j => ord (roots.point i-roots.point j)) s)

/-- On the rational family both the sextic and its leading coefficient use
the same global quadratic twist. -/
abbrev FibreData (a b e : ℤ) (ρ : W) (A : Finset (Fin 2)) (m : ℕ) :=
  ClusterData (FiniteSplitting p a b e ρ) (twisted a b e ρ) A ((p:W)^m) (addVal W)

private theorem assemble {a b e : ℤ} {ρ : W} {A : Finset (Fin 2)} {m : ℕ} (hb : b ≠ 0)
    (he : e ≠ 0) (hρ : ρ^2= -3) (hv : IsUnit (lower a b ρ))
    (T : Configuration (sextic ((upper a b ρ)^6) ((lower a b ρ)^6)) A ((p:W)^m))
    (par : ∀ s, principal A s → Even (nu ((addVal W (twisted a b e ρ).leadingCoeff).toNat:ℤ)
      A (distances A (m:ℕ∞)) s)) : Nonempty (FibreData p a b e ρ A m) := by
  have hc := pow_ne_zero m (show Irreducible (p:W) from WittVector.irreducible p).ne_zero
  have hd := sextic_degree ((upper a b ρ)^6) (pow_ne_zero 6 hv.ne_zero)
  have hs := (configuration_exhausts T hc hd).2.1
  obtain ⟨F⟩ := finite_twisted_splitting p a b e ρ hb hρ hs
  let Q := multiplyConfiguration (2*(e:W)) T
  have scale : (2*(e:W)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast he)
  have d : (twisted a b e ρ).natDegree = 6 := by rw [twisted, natDegree_C_mul scale, hd]
  have vals (i j : Index) : addVal W (Q.point i-Q.point j) = distances A (m:ℕ∞) i j := by
    simpa only [RingHom.id_apply, (show Irreducible (p:W) from WittVector.irreducible p).addVal_pow] using
      pairwise_valuations Q (RingHom.id W) (addVal W) addVal_eq_zero_of_unit i j
  refine ⟨⟨F, d, Q, (configuration_exhausts Q hc d).2.2, proper_odd A, ?_⟩⟩
  intro s hs'
  simpa only [vals] using par s hs'

theorem even_contact_data (hp : 3 < p) (a b e : ℤ) (hb : b ≠ 0) (he : e ≠ 0)
    {ρ : W} (hρ : ρ^2 = -3) (hv : IsUnit (lower a b ρ)) {r : ℕ} (hr : 0 < r)
    (d : Wˣ) (hD : (upper a b ρ)^6 = (lower a b ρ)^6 + ((p:W)^r)^2*(d:W))
    (par : Even (((addVal W (e:W)).toNat:ℤ)+(r:ℤ))) :
    Nonempty (FibreData p a b e ρ Finset.univ r) := by
  let V := (hv.pow 6).unit
  have hV : (V:W) = (lower a b ρ)^6 := (hv.pow 6).unit_spec
  obtain ⟨a', ξ, ⟨T⟩⟩ := (witt_even_contact p hp hr V d).1
  have config := configuration_two T
  rw [hV, ← hD] at config
  obtain ⟨Q⟩ := config
  apply assemble p hb he hρ hv Q
  intro s hs
  rw [lead_order p hp a b e hv]
  exact even_nu r par hs

theorem zero_contact_data (hp : 3 < p) (a b e : ℤ) (hb : b ≠ 0) {ρ : W}
    (hρ : ρ^2 = -3) (hv : IsUnit (lower a b ρ)) (ht : IsUnit (e:W))
    {r : ℕ} (hr : 0 < r) (w : Wˣ) (hu : upper a b ρ=(p:W)^r*(w:W)) :
    Nonempty (FibreData p a b e ρ {0} (2*r)) := by
  let V := (hv.pow 6).unit
  have hV : (V:W) = (lower a b ρ)^6 := (hv.pow 6).unit_spec
  obtain ⟨T⟩ := (witt_zero_contact p hp hr w V).1
  have hu₀ : residue W ((p:W)^r*(w:W))=0 := by
    rw [map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow hr.ne', zero_mul]
  obtain ⟨Q⟩ := configuration_one T hu₀
  have eqn : ((p:W)^r*(w:W))^2=(p:W)^(2*r)*(↑(w^2):W) := by
    rw [mul_pow, Units.val_pow_eq_pow_val, mul_comm 2 r, pow_mul]
  have config := changeRadius Q (w^2) eqn
  rw [hV, ← hu] at config
  have he : e ≠ 0 := by rintro rfl; exact ht.ne_zero (by simp)
  apply assemble p hb he hρ hv config
  intro s hs
  rw [lead_order p hp a b e hv, addVal_eq_zero_iff.mpr ht]
  exact zero_nu r hs

theorem smooth_data (hp : 3 < p) (a b e : ℤ) (hb : b ≠ 0) {ρ : W} (hρ : ρ^2= -3)
    (hu : IsUnit (upper a b ρ)) (hv : IsUnit (lower a b ρ))
    (hD : IsUnit ((upper a b ρ)^6-(lower a b ρ)^6)) (ht : IsUnit (e:W)) :
    Nonempty (FibreData p a b e ρ ∅ 0) := by
  have h₀ := residue_characteristic (k := ResidueField W) p hp
  have hu' := (residue_ne_zero_iff_isUnit _).mpr (hu.pow 6)
  have hv' := (residue_ne_zero_iff_isUnit _).mpr (hv.pow 6)
  have hd' := (residue_ne_zero_iff_isUnit _).mpr hD
  rw [map_sub] at hd'
  have hd := sextic_degree (residue W ((upper a b ρ)^6)) hv'
  have hs := good_fibre_separable h₀.1 h₀.2 hu' hv' hd'
  rw [← sextic_map] at hs
  obtain ⟨Q⟩ := smooth_configuration hs (by rw [sextic_map]; exact hd)
  rw [← pow_zero (p:W)] at Q
  have he : e ≠ 0 := by rintro rfl; exact ht.ne_zero (by simp)
  apply assemble p hb he hρ hv Q
  intro s hs'
  rcases (principal_iff _ _).mp hs' with ⟨rfl,_⟩ | ⟨i,hi,_⟩
  · rw [nu_top, lead_order p hp a b e hv, addVal_eq_zero_iff.mpr ht]
    exact ⟨0,rfl⟩
  · exact (Finset.notMem_empty _ hi).elim

theorem witt_order_map (F : Subfield (Residues p)) [Finite F] (x : WittVector p F) :
    addVal W (inclusion p F x) = addVal (WittVector p F) x := by
  by_cases hx : x=0
  · simp [hx]
  obtain ⟨n,t,ht⟩ := eq_unit_mul_pow_irreducible hx (WittVector.irreducible p)
  rw [ht, map_mul, map_pow, map_natCast, addVal_mul, addVal_mul, addVal_eq_zero_of_unit,
    addVal_eq_zero_iff.mpr (t.isUnit.map _), (show Irreducible (p:W) from WittVector.irreducible p).addVal_pow,
    (show Irreducible (p:WittVector p F) from WittVector.irreducible p).addVal_pow]

private theorem twisted_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b e : ℤ) (ρ : R) : (twisted a b e ρ).map φ = twisted a b e (φ ρ) := by
  simp [twisted, sextic_map, upper, lower, map_ofNat]

set_option maxHeartbeats 1500000 in
/-- The root labels, their full valuation table and the principal-cluster
orders all descend to the very same finite unramified integral extension.
Thus geometric discs may be taken in an algebraic closure of its fraction
field. -/
theorem finite_configuration {a b e : ℤ} {ρ : W} {A : Finset (Fin 2)} {m : ℕ}
    (D : FibreData p a b e ρ A m) :
    let F := D.finiteModel.field
    letI : Finite F := D.finiteModel.finite
    ∃ T : Configuration (twisted a b e D.finiteModel.rho) A ((p:WittVector p F)^m),
      (∀ i, inclusion p F (T.point i)=D.roots.point i) ∧
      (∀ w, (twisted a b e D.finiteModel.rho).IsRoot w ↔ ∃ i, T.point i=w) ∧
      ∀ s, principal A s → Even (nu
        ((addVal (WittVector p F) (twisted a b e D.finiteModel.rho).leadingCoeff).toNat:ℤ) A
        (fun i j => addVal (WittVector p F) (T.point i-T.point j)) s) := by
  let F := D.finiteModel.field
  let : Finite F := D.finiteModel.finite
  let S := WittVector p F
  let ι := inclusion p F
  let f := twisted a b e D.finiteModel.rho
  have hi := inclusion_injective p F
  have hm : f.map ι = twisted a b e ρ := by rw [twisted_map, D.finiteModel.inclusion_rho]
  have hdeg : f.natDegree=6 := by rw [← natDegree_map_eq_of_injective hi, hm, D.degree]
  have nz : f.map ι ≠ 0 := by
    rw [hm]; intro h; have hd := D.degree; simp [h] at hd
  have lifts (i : Index) : ∃ y : S, ι y = D.roots.point i := by
    have hr : D.roots.point i ∈ (f.map ι).roots := (mem_roots nz).mpr
      ((congrArg (fun g : W[X] => g.IsRoot (D.roots.point i)) hm).mpr (D.roots.root i))
    rw [D.finiteModel.splits.roots_map_of_ne_zero nz] at hr
    obtain ⟨x,_,hx⟩ := Multiset.mem_map.mp hr
    exact ⟨x,hx⟩
  choose y hy using lifts
  have vals (i j : Index) : addVal S (y i-y j) = addVal W (D.roots.point i-D.roots.point j) := by
    rw [← witt_order_map p F, map_sub]
    change addVal W (ι (y i)-ι (y j)) = _
    rw [hy, hy]
  have dist (i j : Index) : addVal S (y i-y j) = distances A (m:ℕ∞) i j := by
    rw [vals]
    simpa only [RingHom.id_apply, (show Irreducible (p:W) from WittVector.irreducible p).addVal_pow] using
      pairwise_valuations D.roots (RingHom.id W) (addVal W) addVal_eq_zero_of_unit i j
  have yr (i : Index) : f.IsRoot (y i) := by
    apply (isRoot_map_iff hi).mp
    rw [hm, hy]
    exact D.roots.root i
  let T : Configuration f A ((p:S)^m) := {
    point := y
    root := yr
    deep := fun i j hij same active => by
      have ord : addVal S (y i-y j) = m := by
        rw [dist, distances, ite_eq_right hij, ite_eq_left ⟨same,active⟩]
      have assoc := (addVal_eq_iff_associated ((p:S)^m) (y i-y j)).mp
        ((show Irreducible (p:S) from WittVector.irreducible p).addVal_pow m |>.trans ord.symm)
      obtain ⟨z,hz⟩ := assoc
      exact ⟨z,hz.symm⟩
    shallow := fun i j hij h => addVal_eq_zero_iff.mp (by rw [dist, distances, ite_eq_right hij, ite_eq_right h]) }
  have lead : addVal S f.leadingCoeff = addVal W (twisted a b e ρ).leadingCoeff := by
    calc
      _ = addVal W (ι f.leadingCoeff) := (witt_order_map p F _).symm
      _ = addVal W (f.map ι).leadingCoeff := congrArg (addVal W) (leadingCoeff_map_of_injective hi f).symm
      _ = _ := congrArg (fun g : W[X] => addVal W g.leadingCoeff) hm
  refine ⟨T, hy, (configuration_exhausts T (pow_ne_zero _ (WittVector.irreducible p).ne_zero) hdeg).2.2, ?_⟩
  intro s hs
  change Even (nu ((addVal S f.leadingCoeff).toNat:ℤ) A (fun i j => addVal S (y i-y j)) s)
  simpa only [lead, vals] using D.parity s hs

private theorem strict_radical (hp : 3 < p) : ∃ z : W, z^2 = -2 := by
  let k := ResidueField W
  have h₂ := (residue_characteristic (k := k) p hp).1
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (-2:k) (by decide : 0<2)
  have hn : z ≠ 0 := by intro h; simp [h,h₂] at hz
  have der : (X^2+2 : W[X]).derivative = 2*X := by simp [derivative_pow,map_ofNat]
  obtain ⟨r,hr,_⟩ := liftSimple (X^2+2 : W[X]) z (by simp [hz])
    (by rw [der]; simpa only [eval₂_mul, eval₂_X, eval₂_ofNat] using mul_ne_zero h₂ hn)
  exact ⟨r, by simpa [IsRoot, eq_neg_iff_add_eq_zero] using hr⟩

theorem reciprocal_radical (hp : 3 < p) {a b e : ℤ} {ρ : W} (D : FiniteSplitting p a b e ρ) :
    ∃ r : WittVector p D.field, r^2 = -2 := by
  obtain ⟨z,hz⟩ := strict_radical p hp
  obtain ⟨r,hr⟩ := D.radical z hz
  refine ⟨r, inclusion_injective p D.field ?_⟩
  rw [map_pow, map_neg, map_ofNat, hr, hz]

/-- The reciprocal isomorphism of the actual localized chart rings is defined
already over the fraction field of the finite unramified splitting DVR. -/
theorem finite_reciprocal_chart (hp : 3 < p) {a b e : ℤ} {ρ : W} (D : FiniteSplitting p a b e ρ) :
    letI : Finite D.field := D.finite
    let S := WittVector p D.field
    let K := FractionRing S
    let q := algebraMap S K D.rho
    let U := (upper a b q)^6
    let V := (lower a b q)^6
    Nonempty (PicardConjugation.ChartRing U V (e:K) ≃ₐ[K] PicardConjugation.ChartRing V U (e:K)) := by
  let S := WittVector p D.field
  let K := FractionRing S
  let : Finite D.field := D.finite
  let : CharZero S := charZero_of_injective_ringHom (f := fromPadics p D.field)
    ((WittVector.map_injective _ (ZMod.castHom (by simp) D.field).injective).comp (WittVector.equiv p).symm.injective)
  obtain ⟨r,hr⟩ := reciprocal_radical p hp D
  have eqn : (algebraMap S K r)^2 = -2 := by rw [← map_pow, hr, map_neg, map_ofNat]
  exact ⟨PicardConjugation.chartAlgEquiv _ _ _ _ eqn⟩

open PrimitiveTwist ZInQ.QualitativeHeight

set_option maxHeartbeats 1500000 in
/-- At every nonodd contact of the rational family, the specified root of
`-3` or its negative gives all cluster and splitting data. The negative
choice is the reciprocal chart, whose change of ordinate uses the square
root of `-2` in the same unramified extension. -/
theorem rational_fibre_data (hp : 3 < p) (s : ℚ) (hb : primitiveBranch s ≠ 0)
    (hev : ¬ Odd (padicValRat p (primitiveBranch s))) {ρ : W} (hρ : ρ^2= -3) :
    ∃ ρ' : W, (ρ'=ρ ∨ ρ'= -ρ) ∧ ∃ (A : Finset (Fin 2)) (m : ℕ),
      Nonempty (FibreData p s.num s.den (twist s) ρ' A m) := by
  have den : (s.den:ℤ) ≠ 0 := by exact_mod_cast s.den_nz
  have te : (twist s : ℤ) ≠ 0 := by exact_mod_cast (positive s).ne'
  have hu : upper s.num (s.den:ℤ) ρ = plus p s ρ := by simp [upper,plus]
  have hv : lower s.num (s.den:ℤ) ρ = minus p s ρ := by simp [lower,minus]
  have hu' : upper s.num (s.den:ℤ) (-ρ) = minus p s ρ := by simp [upper,minus,sub_eq_add_neg]
  have hv' : lower s.num (s.den:ℤ) (-ρ) = plus p s ρ := by simp [lower,plus]
  cases cases_of_even p hp s hb hev hρ with
  | distinct h₁ h₂ h₃ h₄ =>
    refine ⟨ρ,Or.inl rfl,∅,0,smooth_data p hp _ _ _ den hρ (hu ▸ h₁) (hv ▸ h₂) ?_ ?_⟩
    · simpa only [hu,hv] using h₃
    · simpa only [Int.cast_natCast] using h₄
  | zeroFirst r hr w h₁ h₂ h₃ =>
    exact ⟨ρ,Or.inl rfl,{0},2*r,zero_contact_data p hp _ _ _ den hρ (hv ▸ h₂)
      (by simpa only [Int.cast_natCast] using h₃) hr w (hu.trans h₁)⟩
  | zeroSecond r hr w h₁ h₂ h₃ =>
    exact ⟨-ρ,Or.inr rfl,{0},2*r,zero_contact_data p hp _ _ _ den (by simpa using hρ)
      (hv' ▸ h₂) (by simpa only [Int.cast_natCast] using h₃) hr w (hu'.trans h₁)⟩
  | twoTriples r hr d _ h₂ h₃ h₄ =>
    refine ⟨ρ,Or.inl rfl,Finset.univ,r,even_contact_data p hp _ _ _ den te hρ (hv ▸ h₂) hr d ?_ ?_⟩
    · simpa only [hu,hv] using h₃
    · rw [Int.cast_natCast,h₄,ENat.toNat_natCast, Int.even_iff]
      omega

end Arithmetic

end
end ZOverQ.Qualitative.LocalSupport

#print axioms ZOverQ.Qualitative.LocalSupport.finite_ring_for_family
#print axioms ZOverQ.Qualitative.LocalSupport.primitive_chart_scale
#print axioms ZOverQ.Qualitative.LocalSupport.witt_unramified
#print axioms ZOverQ.Qualitative.LocalSupport.witt_finite_etale
#print axioms ZOverQ.Qualitative.LocalSupport.witt_fraction_unramified
#print axioms ZOverQ.Qualitative.LocalSupport.relative_finite_etale
#print axioms ZOverQ.Qualitative.LocalSupport.finite_twisted_splitting
#print axioms ZOverQ.Qualitative.LocalSupport.geometric_disc
#print axioms ZOverQ.Qualitative.LocalSupport.even_nu
#print axioms ZOverQ.Qualitative.LocalSupport.zero_nu
#print axioms ZOverQ.Qualitative.LocalSupport.smooth_data
#print axioms ZOverQ.Qualitative.LocalSupport.zero_contact_data
#print axioms ZOverQ.Qualitative.LocalSupport.even_contact_data
#print axioms ZOverQ.Qualitative.LocalSupport.geometric_iff
#print axioms ZOverQ.Qualitative.LocalSupport.geometric_roots
#print axioms ZOverQ.Qualitative.LocalSupport.finite_configuration
#print axioms ZOverQ.Qualitative.LocalSupport.reciprocal_radical
#print axioms ZOverQ.Qualitative.LocalSupport.finite_reciprocal_chart
#print axioms ZOverQ.Qualitative.LocalSupport.rational_fibre_data
