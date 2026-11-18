import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.Abel

/-! Uniform finite Galois factorization of splitting cochains for trivial coefficients.

The arithmetic input to `rational_uniform_splitting` is Tate's vanishing in continuous
cohomology for the **discrete** module `ℚ̄ˣ` with **trivial** Galois action. The hypothesis
uses `LocallyConstant` on the absolute Galois group with its Krull topology. Ribet gives
this precise coefficient convention and the resulting splitting cochain in §6, Theorem 6.3,
of [Abelian varieties over ℚ and modular forms](https://math.berkeley.edu/~ribet/Articles/korea.pdf).
-/

namespace ZOverQ.Qualitative.UniformDescent

open scoped Topology
open groupCohomology

noncomputable section

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- Restriction from the ambient Galois extension to a finite Galois intermediate field. -/
abbrev restriction (L : FiniteGaloisIntermediateField k Ω) : Gal(Ω/k) →* Gal(L/k) :=
  AlgEquiv.restrictNormalHom L

/-- Restriction between nested finite Galois intermediate fields. -/
def finiteRestriction {L M : FiniteGaloisIntermediateField k Ω} (hLM : L ≤ M) :
    Gal(M/k) →* Gal(L/k) :=
  letI : Algebra L M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  letI : IsScalarTower k L M := IsScalarTower.of_algebraMap_eq' rfl
  AlgEquiv.restrictNormalHom L

omit [IsGalois k Ω] in
@[simp] theorem finiteRestriction_restriction {L M : FiniteGaloisIntermediateField k Ω}
    (h : L ≤ M) (σ : Gal(Ω/k)) : finiteRestriction h (restriction M σ) = restriction L σ := by
  let : Algebra L M := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower k L M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq' rfl
  exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L M σ).symm

/-- A finite set of locally constant maps on a Galois group factors simultaneously through
one finite Galois extension containing a prescribed finite Galois intermediate field. -/
theorem common_finite_galois_field (L : FiniteGaloisIntermediateField k Ω)
    {I A : Type*} [Finite I] (b : I → LocallyConstant Gal(Ω/k) A) :
    ∃ M : FiniteGaloisIntermediateField k Ω, L ≤ M ∧
      ∃ B : I → Gal(M/k) → A, ∀ i σ, B i (restriction M σ) = b i σ := by
  classical
  let f := LocallyConstant.unflip b
  let P := Gal(Ω/k)
  let S : Set (P × P) := {p | f (p.1 * p.2) = f p.1}
  have hopen : IsOpen S :=
    ((f.isLocallyConstant.comp_continuous continuous_mul).prodMk
      (f.isLocallyConstant.comp_continuous continuous_fst)) {v | v.1 = v.2}
  obtain ⟨U, V, _, hV, hU, hone, hUV⟩ := generalized_tube_lemma
    (isCompact_univ (X := P)) (isCompact_singleton (x := (1 : P))) hopen (by
      rintro ⟨g,n⟩ ⟨_,hn⟩
      obtain rfl : n = 1 := hn
      change f (g * 1) = f g
      rw [mul_one])
  obtain ⟨M₀, hM₀⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
    (k := k) (K := Ω) V).mp (hV.mem_nhds (hone (Set.mem_singleton _)))
  let M := L ⊔ M₀
  have hminor : M₀.toIntermediateField ≤ M.toIntermediateField :=
    show M₀ ≤ M from le_sup_right
  have hfactor {σ τ : P} (heq : restriction M σ = restriction M τ) : f σ = f τ := by
    have hn : σ⁻¹ * τ ∈ M.fixingSubgroup :=
      (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff _ M).2 (by
        change restriction M (σ⁻¹ * τ) = 1
        rw [map_mul, map_inv, heq, inv_mul_cancel])
    have h : f (σ * (σ⁻¹ * τ)) = f σ :=
      hUV (a := (σ, σ⁻¹ * τ)) ⟨hU (Set.mem_univ σ),
        hM₀ (M₀.toIntermediateField.fixingSubgroup_antitone hminor hn)⟩
    simpa using h.symm
  refine ⟨M, le_sup_left, fun i g => b i (g.liftNormal Ω), ?_⟩
  intro i σ
  exact congrFun (hfactor ((restriction M σ).restrict_liftNormal Ω)) i

/-- The usual degree-one inhomogeneous differential with trivial action. -/
def coboundary {G A : Type*} [Mul G] [AddCommGroup A] (b : G → A) (g h : G) : A :=
  b h - b (g*h) + b g

abbrev trivialRepresentation (G A : Type) [Group G] [AddCommGroup A] := Rep.trivial ℤ G A

/-- Finiteness of the usual second cohomology group and locally constant primitives for each
inflated class suffice to choose one finite field of definition for the domains of all primitives. -/
theorem uniform_finite_galois_splitting (L : FiniteGaloisIntermediateField k Ω)
    (A : Type) [AddCommGroup A] [Finite (H2 (trivialRepresentation Gal(L/k) A))]
    (hTate : ∀ c : cocycles₂ (trivialRepresentation Gal(L/k) A),
      ∃ b : LocallyConstant Gal(Ω/k) A, ∀ σ τ : Gal(Ω/k),
        c (restriction L σ, restriction L τ) = coboundary b σ τ) :
    ∃ (M : FiniteGaloisIntermediateField k Ω) (hLM : L ≤ M),
      ∀ c : cocycles₂ (trivialRepresentation Gal(L/k) A), ∃ b : Gal(M/k) → A,
        ∀ g h, c (finiteRestriction hLM g, finiteRestriction hLM h) = coboundary b g h := by
  classical
  let V := trivialRepresentation Gal(L/k) A
  have hreps (i : H2 V) : ∃ c : cocycles₂ V, H2π V c = i :=
    H2_induction_on i fun c => ⟨c, rfl⟩
  choose r hr using hreps
  choose b hb using fun i => hTate (r i)
  obtain ⟨M, hLM, B, hB⟩ := common_finite_galois_field L b
  refine ⟨M, hLM, ?_⟩
  intro c
  let i := H2π V c
  have hclass : H2π V c = H2π V (r i) := (hr i).symm
  obtain ⟨a, ha⟩ := (H2π_eq_iff c (r i)).1 hclass
  have hrep (g h : Gal(M/k)) :
      (r i) (finiteRestriction hLM g, finiteRestriction hLM h) = coboundary (B i) g h := by
    obtain ⟨σ,rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω g
    obtain ⟨τ,rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω h
    change (r i) (finiteRestriction hLM (restriction M σ), finiteRestriction hLM (restriction M τ)) =
      B i (restriction M τ) - B i (restriction M σ * restriction M τ) + B i (restriction M σ)
    rw [finiteRestriction_restriction, finiteRestriction_restriction, ← map_mul, hB, hB, hB]
    exact hb i σ τ
  refine ⟨fun g => B i g + a (finiteRestriction hLM g), ?_⟩
  intro g h
  let z := finiteRestriction hLM g
  let w := finiteRestriction hLM h
  have hd : coboundary a z w = c (z,w) - (r i) (z,w) := congrFun ha (z,w)
  calc
    c (z,w) = (r i) (z,w) + coboundary a z w := by rw [hd]; abel
    _ = _ := by
      rw [hrep]
      simp only [coboundary, map_mul, z, w]
      abel

set_option maxHeartbeats 800000 in
/-- A finite group of order `n` has finite `H²` with trivial coefficients in an abelian
 group on which `n` is surjective with finite kernel. Summing the cocycle identity over the
 last variable gives a primitive for `n • c`. Subtracting an `n`-th root of that primitive
 leaves a cocycle with values in the finite `n`-torsion. -/
theorem finite_second_cohomology (G A : Type) [Group G] [Fintype G] [AddCommGroup A]
    (hdiv : Function.Surjective (fun a : A => Fintype.card G • a))
    [Finite {a : A // Fintype.card G • a = 0}] :
    Finite (H2 (trivialRepresentation G A)) := by
  classical
  let V := trivialRepresentation G A
  let n := Fintype.card G
  let T := {c : cocycles₂ V // ∀ x, n • c x = 0}
  let vals (z : T) (x : G × G) : {a : A // n • a = 0} := ⟨z.1 x, z.2 x⟩
  have hvinj : Function.Injective vals := by
    intro z w he
    apply Subtype.ext
    apply Subtype.ext
    exact funext fun x => congrArg Subtype.val (congrFun he x)
  let : Finite T := Finite.of_injective vals hvinj
  apply Finite.of_surjective (fun z : T => H2π V z.1)
  intro v
  refine H2_induction_on (A := V) (C := fun x => ∃ z : T, H2π V z.1 = x) v ?_
  intro c
  let S (g : G) : A := ∑ t : G, c (g,t)
  have hnorm (g h : G) : coboundary S g h = n • c (g,h) := by
    have hsum : (∑ t : G, (c (g*h,t) + c (g,h))) = ∑ t : G, (c (h,t) + c (g,h*t)) :=
      Finset.sum_congr rfl fun t _ => (mem_cocycles₂_iff (A := V) c).1 c.2 g h t
    have hperm : (∑ t : G, c (g,h*t)) = S g := Equiv.sum_comp (Equiv.mulLeft h) (fun t => c (g,t))
    have heq : S (g*h) + n • c (g,h) = S h + S g := by
      simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hperm, S, n] using hsum
    unfold coboundary
    rw [← add_left_cancel_iff (a := S (g*h))]
    rw [heq]
    abel
  choose a ha using fun g => hdiv (S g)
  change ∀ g, n • a g = S g at ha
  let d : cocycles₂ V := ⟨d₁₂ V a, d₁₂_apply_mem_cocycles₂ (A := V) a⟩
  have hd (g h : G) : n • d (g,h) = n • c (g,h) := by
    change n • (a h - a (g*h) + a g) = _
    rw [nsmul_add, nsmul_sub, ha, ha, ha]
    exact hnorm g h
  have hzero : H2π V d = 0 := (H2π_eq_zero_iff d).2 ⟨a, rfl⟩
  refine ⟨⟨c - d, ?_⟩, ?_⟩
  · rintro ⟨g,h⟩
    change n • (c (g,h) - d (g,h)) = 0
    rw [nsmul_sub, hd, sub_self]
  · change H2π V (c - d) = H2π V c
    rw [map_sub, hzero, sub_zero]

/-- The Schur finiteness input for the discrete trivial multiplicative group of an
algebraically closed field, using the finite group of roots of unity. -/
theorem finite_second_cohomology_units (G F : Type) [Group G] [Finite G] [Field F] [IsAlgClosed F] :
    Finite (H2 (trivialRepresentation G (Additive Fˣ))) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let n := Fintype.card G
  have hn : 0 < n := Fintype.card_pos
  let : NeZero n := ⟨hn.ne'⟩
  have hdiv (a : Additive Fˣ) : ∃ z : Additive Fˣ, n • z = a := by
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (a.toMul : F) hn
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hr
      exact a.toMul.ne_zero hr.symm
    refine ⟨Additive.ofMul (Units.mk0 r hr0), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    exact hr
  let : Finite {a : Additive Fˣ // n • a = 0} :=
    Finite.of_injective (fun a => (⟨a.1.toMul, a.2⟩ : rootsOfUnity n F))
      (fun _ _ e => Subtype.ext (congrArg Subtype.val e))
  exact finite_second_cohomology G (Additive Fˣ) hdiv

abbrev Qbar := AlgebraicClosure ℚ
abbrev coefficients := Additive Qbarˣ

/-- The coefficient embedding on units. -/
abbrev rationalUnit : ℚˣ →* Qbarˣ := Units.map (algebraMap ℚ Qbar).toMonoidHom

/-- Tate's individual continuous splitting statement implies one finite Galois extension
`M/ℚ` containing `L` on whose Galois group **all** rational-valued multiplicative
2-cocycles on `Gal(L/ℚ)` have algebraic-valued primitives. Coefficients have trivial action
and the discrete topology. -/
theorem rational_uniform_splitting (L : FiniteGaloisIntermediateField ℚ Qbar)
    (hTate : ∀ c : cocycles₂ (trivialRepresentation Gal(L/ℚ) coefficients),
      ∃ b : LocallyConstant Gal(Qbar/ℚ) coefficients, ∀ σ τ : Gal(Qbar/ℚ),
        c (restriction L σ, restriction L τ) = coboundary b σ τ) :
    ∃ (M : FiniteGaloisIntermediateField ℚ Qbar) (hLM : L ≤ M),
      ∀ c : Gal(L/ℚ) × Gal(L/ℚ) → ℚˣ,
        (∀ g h j, c (g*h,j) * c (g,h) = c (h,j) * c (g,h*j)) →
        ∃ b : Gal(M/ℚ) → Qbarˣ, ∀ g h,
          rationalUnit (c (finiteRestriction hLM g, finiteRestriction hLM h)) = b g * b h / b (g*h) := by
  let : Finite (H2 (trivialRepresentation Gal(L/ℚ) coefficients)) :=
    finite_second_cohomology_units Gal(L/ℚ) Qbar
  obtain ⟨M,hLM,hM⟩ := uniform_finite_galois_splitting L coefficients hTate
  refine ⟨M,hLM,?_⟩
  intro c hc
  let v : Gal(L/ℚ) × Gal(L/ℚ) → coefficients := fun x => Additive.ofMul (rationalUnit (c x))
  have hv : v ∈ cocycles₂ (trivialRepresentation Gal(L/ℚ) coefficients) := by
    apply (mem_cocycles₂_iff (A := trivialRepresentation Gal(L/ℚ) coefficients) v).2
    intro g h j
    change rationalUnit (c (g*h,j)) * rationalUnit (c (g,h)) =
      rationalUnit (c (h,j)) * rationalUnit (c (g,h*j))
    rw [← map_mul, ← map_mul, hc]
  obtain ⟨b,hb⟩ := hM ⟨v,hv⟩
  refine ⟨fun g => (b g).toMul, ?_⟩
  intro g h
  have he : rationalUnit (c (finiteRestriction hLM g, finiteRestriction hLM h)) =
      (b h).toMul / (b (g*h)).toMul * (b g).toMul := hb g h
  rw [he, div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

/-- The number field generated by the values of a multiplicative splitting cochain. -/
def coefficientField {G : Type} (b : G → Qbarˣ) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ (Set.range fun g => (b g : Qbar))

/-- Projective multiplication by rational factors makes the span of all cochain values a field. -/
theorem coefficientField_eq_span {G : Type} [Group G] (b : G → Qbarˣ) (c : G × G → ℚˣ)
    (hb : ∀ g h, rationalUnit (c (g,h)) = b g * b h / b (g*h)) :
    (coefficientField b).toSubalgebra.toSubmodule =
      Submodule.span ℚ (Set.range fun g => (b g : Qbar)) := by
  let V := Submodule.span ℚ (Set.range fun g => (b g : Qbar))
  have gen (g : G) : (b g : Qbar) ∈ V := Submodule.subset_span ⟨g,rfl⟩
  have he : rationalUnit (c (1,1)) = b 1 := by simpa using hb 1 1
  have hunit : ((↑((c (1,1))⁻¹) : ℚ) • (b 1 : Qbar)) = 1 := by
    rw [Algebra.smul_def]
    change ((rationalUnit ((c (1,1))⁻¹) * b 1 : Qbarˣ) : Qbar) = 1
    rw [← he, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h_one : (1 : Qbar) ∈ V := hunit ▸ V.smul_mem _ (gen 1)
  have h_mul (x y : Qbar) (hx : x ∈ V) (hy : y ∈ V) : x * y ∈ V := by
    refine Submodule.span_induction₂ (p := fun x y _ _ => x*y ∈ V) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro _ _ ⟨g,rfl⟩ ⟨h,rfl⟩
      have e : b g * b h = rationalUnit (c (g,h)) * b (g*h) := by rw [hb, div_mul_cancel]
      have ee : (b g : Qbar) * b h = (↑(c (g,h)) : ℚ) • (b (g*h) : Qbar) :=
        by rw [Algebra.smul_def]; exact congrArg Units.val e
      rw [ee]
      exact V.smul_mem _ (gen _)
    · intro y _; simp [V]
    · intro x _; simp [V]
    · intro x y z _ _ _ hx hy; simpa only [add_mul] using V.add_mem hx hy
    · intro x y z _ _ _ hy hz; simpa only [mul_add] using V.add_mem hy hz
    · intro r x y _ _ h; simpa only [smul_mul_assoc] using V.smul_mem r h
    · intro r x y _ _ h; simpa only [mul_smul_comm] using V.smul_mem r h
  let E : IntermediateField ℚ Qbar := subalgebraEquivIntermediateField (V.toSubalgebra h_one h_mul)
  apply le_antisymm
  · have hi : coefficientField b ≤ E := IntermediateField.adjoin_le_iff.mpr (by
      rintro _ ⟨g,rfl⟩
      exact gen g)
    exact hi
  · exact Submodule.span_le.mpr (IntermediateField.subset_adjoin ℚ _)

/-- The field of values of a splitting cochain on `G` has degree at most `|G|`. -/
theorem coefficientField_degree_le {G : Type} [Group G] [Finite G] (b : G → Qbarˣ)
    (c : G × G → ℚˣ) (hb : ∀ g h, rationalUnit (c (g,h)) = b g * b h / b (g*h)) :
    FiniteDimensional ℚ (coefficientField b) ∧ Module.finrank ℚ (coefficientField b) ≤ Nat.card G := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let v (g : G) : Qbar := b g
  change FiniteDimensional ℚ (coefficientField b).toSubalgebra.toSubmodule ∧
    Module.finrank ℚ (coefficientField b).toSubalgebra.toSubmodule ≤ Nat.card G
  rw [coefficientField_eq_span b c hb]
  refine ⟨FiniteDimensional.span_of_finite ℚ (Set.finite_range v), ?_⟩
  exact (finrank_span_le_card (Set.range v)).trans (by
    rw [Set.toFinset_card, ← Fintype.card_eq_nat_card]
    exact Fintype.card_range_le v)

/-- The single field `M` also bounds the coefficient degree in every rational splitting problem. -/
theorem rational_uniform_splitting_degree (L : FiniteGaloisIntermediateField ℚ Qbar)
    (hTate : ∀ c : cocycles₂ (trivialRepresentation Gal(L/ℚ) coefficients),
      ∃ b : LocallyConstant Gal(Qbar/ℚ) coefficients, ∀ σ τ : Gal(Qbar/ℚ),
        c (restriction L σ, restriction L τ) = coboundary b σ τ) :
    ∃ (M : FiniteGaloisIntermediateField ℚ Qbar) (hLM : L ≤ M),
      ∀ c : Gal(L/ℚ) × Gal(L/ℚ) → ℚˣ,
        (∀ g h j, c (g*h,j) * c (g,h) = c (h,j) * c (g,h*j)) →
        ∃ b : Gal(M/ℚ) → Qbarˣ, (∀ g h,
          rationalUnit (c (finiteRestriction hLM g, finiteRestriction hLM h)) = b g * b h / b (g*h)) ∧
          FiniteDimensional ℚ (coefficientField b) ∧
          Module.finrank ℚ (coefficientField b) ≤ Module.finrank ℚ M := by
  obtain ⟨M,hLM,hM⟩ := rational_uniform_splitting L hTate
  refine ⟨M,hLM,?_⟩
  intro c hc
  obtain ⟨b,hb⟩ := hM c hc
  refine ⟨b,hb,?_⟩
  rw [← IsGalois.card_aut_eq_finrank ℚ M]
  exact coefficientField_degree_le b (fun p => c (finiteRestriction hLM p.1,finiteRestriction hLM p.2)) hb

/-- A cochain value as an element of its coefficient field. -/
def coefficientValue {G : Type} (b : G → Qbarˣ) (g : G) : coefficientField b :=
  ⟨b g, IntermediateField.subset_adjoin ℚ _ ⟨g,rfl⟩⟩

/-- A splitting cochain takes unit values already in its coefficient field. -/
def coefficientUnit {G : Type} (b : G → Qbarˣ) (g : G) : (coefficientField b)ˣ :=
  Units.mk0 (coefficientValue b g) (fun h => (b g).ne_zero (congrArg Subtype.val h))

/-- Evaluation of the rational regular basis on the splitting cochain. -/
def coefficientEvaluation {G : Type} [Fintype G] (b : G → Qbarˣ) :
    (G → ℚ) →ₗ[ℚ] coefficientField b := Fintype.linearCombination ℚ (coefficientValue b)

/-- Multiplication of basis values has precisely the rational structure coefficients `c`. -/
theorem coefficientValue_mul {G : Type} [Group G] (b : G → Qbarˣ) (c : G × G → ℚˣ)
    (hb : ∀ g h, rationalUnit (c (g,h)) = b g * b h / b (g*h)) (g h : G) :
    coefficientValue b g * coefficientValue b h = (↑(c (g,h)) : ℚ) • coefficientValue b (g*h) := by
  rw [Algebra.smul_def]
  apply Subtype.ext
  change ((b g * b h : Qbarˣ) : Qbar) = ((rationalUnit (c (g,h)) * b (g*h) : Qbarˣ) : Qbar)
  rw [hb, div_mul_cancel]

/-- Every element of the coefficient field is the evaluation of a rational regular vector. -/
theorem coefficientEvaluation_surjective {G : Type} [Group G] [Fintype G] (b : G → Qbarˣ)
    (c : G × G → ℚˣ) (hb : ∀ g h, rationalUnit (c (g,h)) = b g * b h / b (g*h)) :
    Function.Surjective (coefficientEvaluation b) := by
  intro z
  let v (g : G) : Qbar := b g
  have hz : (z : Qbar) ∈ LinearMap.range (Fintype.linearCombination ℚ v) := by
    rw [Fintype.range_linearCombination, ← coefficientField_eq_span b c hb]
    exact z.2
  obtain ⟨a,ha⟩ := hz
  refine ⟨a, Subtype.ext ?_⟩
  calc
    ((coefficientEvaluation b a : coefficientField b) : Qbar) =
        (coefficientField b).val (∑ g, a g • coefficientValue b g) := rfl
    _ = Fintype.linearCombination ℚ v a := by
      rw [map_sum, Fintype.linearCombination_apply]
      exact Finset.sum_congr rfl fun g _ => (coefficientField b).val.toLinearMap.map_smul (a g) _
    _ = _ := ha

/-- The left action of a basis vector in the twisted regular representation. -/
def twistedLeftShift {G : Type} [Group G] (c : G × G → ℚˣ) (g : G) :
    (G → ℚ) →ₗ[ℚ] (G → ℚ) where
  toFun v x := (c (g,g⁻¹*x) : ℚ) * v (g⁻¹*x)
  map_add' _ _ := funext fun _ => mul_add _ _ _
  map_smul' r _ := funext fun _ => mul_left_comm _ r _

/-- The twisted left-regular action descends to multiplication in the coefficient field. -/
theorem coefficientEvaluation_twistedLeftShift {G : Type} [Group G] [Fintype G]
    (b : G → Qbarˣ) (c : G × G → ℚˣ)
    (hb : ∀ g h, rationalUnit (c (g,h)) = b g * b h / b (g*h)) (g : G) (v : G → ℚ) :
    coefficientEvaluation b (twistedLeftShift c g v) = coefficientValue b g * coefficientEvaluation b v := by
  classical
  calc
    _ = ∑ z : G, ((c (g,z) : ℚ) * v z) • coefficientValue b (g*z) := by
      symm
      have he := Equiv.sum_comp (Equiv.mulLeft g)
        (fun y => twistedLeftShift c g v y • coefficientValue b y)
      change (∑ z : G, ((c (g,g⁻¹*(g*z)) : ℚ) * v (g⁻¹*(g*z))) • coefficientValue b (g*z)) =
        coefficientEvaluation b (twistedLeftShift c g v) at he
      simpa only [inv_mul_cancel_left] using he
    _ = _ := by
      change _ = coefficientValue b g * ∑ z : G, v z • coefficientValue b z
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [mul_smul_comm, coefficientValue_mul b c hb, smul_smul, mul_comm (c (g,z) : ℚ) (v z)]

/-- Each twisted left shift is invertible. -/
def twistedLeftShiftEquiv {G : Type} [Group G] (c : G × G → ℚˣ) (g : G) :
    (G → ℚ) ≃ₗ[ℚ] (G → ℚ) :=
  { twistedLeftShift c g with
    invFun := fun f x => (↑((c (g,x))⁻¹) : ℚ) * f (g*x)
    left_inv := fun f => funext fun x => by
      change (↑((c (g,x))⁻¹) : ℚ) * ((c (g,g⁻¹*(g*x)) : ℚ) * f (g⁻¹*(g*x))) = f x
      rw [inv_mul_cancel_left, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    right_inv := fun f => funext fun x => by
      change (c (g,g⁻¹*x) : ℚ) * ((↑((c (g,g⁻¹*x))⁻¹) : ℚ) * f (g*(g⁻¹*x))) = f x
      rw [mul_inv_cancel_left, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] }

/-- The regular matrices have the prescribed cocycle as their factor set. -/
theorem twistedLeftShift_mul {G : Type} [Group G] (c : G × G → ℚˣ)
    (hc : ∀ g h j, c (g*h,j) * c (g,h) = c (h,j) * c (g,h*j)) (g h : G) (v : G → ℚ) :
    twistedLeftShift c g (twistedLeftShift c h v) = (c (g,h) : ℚ) • twistedLeftShift c (g*h) v := by
  funext x
  let z := (g*h)⁻¹*x
  have hg : g⁻¹*x = h*z := by simp [z, mul_assoc]
  have hh : h⁻¹*(g⁻¹*x) = z := by rw [hg,inv_mul_cancel_left]
  change (c (g,g⁻¹*x) : ℚ) * ((c (h,h⁻¹*(g⁻¹*x)) : ℚ) * v (h⁻¹*(g⁻¹*x))) =
    (c (g,h) : ℚ) * ((c (g*h,z) : ℚ) * v z)
  rw [hh,hg]
  have he := congrArg Units.val (hc g h z)
  simp only [Units.val_mul] at he
  calc
    _ = ((c (h,z) : ℚ) * (c (g,h*z) : ℚ)) * v z := by ac_rfl
    _ = ((c (g*h,z) : ℚ) * (c (g,h) : ℚ)) * v z := congrArg (· * v z) he.symm
    _ = _ := by ac_rfl

#print axioms twistedLeftShiftEquiv
#print axioms twistedLeftShift_mul
#print axioms coefficientValue_mul
#print axioms coefficientEvaluation_surjective
#print axioms coefficientEvaluation_twistedLeftShift

#print axioms coefficientField_eq_span
#print axioms coefficientField_degree_le
#print axioms rational_uniform_splitting_degree

#print axioms common_finite_galois_field
#print axioms uniform_finite_galois_splitting
#print axioms finite_second_cohomology
#print axioms finite_second_cohomology_units
#print axioms rational_uniform_splitting

end
end ZOverQ.Qualitative.UniformDescent
