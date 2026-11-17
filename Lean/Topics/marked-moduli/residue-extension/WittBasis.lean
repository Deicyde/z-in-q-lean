import UnramifiedWitt
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Smooth.Fiber

/-! Integral coordinates in the unramified quadratic Witt extension. -/
noncomputable section
namespace ZInQBlueprint.ResidueExtension
variable (p : ℕ) [Fact p.Prime]
abbrev WittAut := QuadraticField p ≃ₐ[ZMod p] QuadraticField p

private theorem aut_count : Nat.card (WittAut p) = 2 :=
  (IsGalois.card_aut_eq_finrank (ZMod p) (QuadraticField p)).trans (quadratic_degree p)

/-- A lift of a residue generator and 1 give unique integral coordinates over ℤp. -/
theorem integral_coordinates : ∃ t : IntegralField p,
    Function.Bijective (fun ab : ℤ_[p] × ℤ_[p] => fromPadics p ab.1 + fromPadics p ab.2*t) := by
  classical
  obtain ⟨g, hg, huniq⟩ := (Nat.card_eq_two_iff' (1 : WittAut p)).mp (aut_count p)
  have invol (z : QuadraticField p) : g (g z) = z := by
    have h2 : g*g=1 := by simpa only [aut_count, pow_two] using (pow_card_eq_one' (x := g))
    exact DFunLike.congr_fun h2 z
  let T : IntegralField p →+* IntegralField p := WittVector.map g.toRingHom
  have hT (x : IntegralField p) : T (T x) = x := by
    ext i
    exact invol _
  have base (a : ℤ_[p]) : T (fromPadics p a) = fromPadics p a := by
    ext i
    exact g.commutes _
  have fixed (x : IntegralField p) (hx : T x = x) : ∃ a : ℤ_[p], fromPadics p a = x := by
    have each (i : ℕ) : x.coeff i ∈ Set.range (algebraMap (ZMod p) (QuadraticField p)) := by
      apply (IsGalois.mem_range_algebraMap_iff_fixed (x.coeff i)).mpr
      intro f
      by_cases h : f = 1
      · simp [h]
      · rw [huniq f h]
        exact congrArg (fun v : IntegralField p => v.coeff i) hx
    choose b hb using each
    refine ⟨WittVector.equiv p (WittVector.mk p b), ?_⟩
    ext i
    simpa [fromPadics] using hb i
  have moved : ∃ z : QuadraticField p, g z ≠ z := by
    by_contra! h
    apply hg
    ext z
    exact h z
  obtain ⟨z, hz⟩ := moved
  obtain ⟨t, ht⟩ := WittVector.constantCoeff_surjective p z
  have unit : IsUnit (t - T t) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    change WittVector.constantCoeff (t-T t) ≠ 0
    rw [map_sub]
    change t.coeff 0 - g (t.coeff 0) ≠ 0
    change t.coeff 0 = z at ht
    exact sub_ne_zero.mpr (ht ▸ hz.symm)
  refine ⟨t, ?_, ?_⟩
  · rintro ⟨a,b⟩ ⟨c,d⟩ h
    change fromPadics p a + fromPadics p b*t = fromPadics p c + fromPadics p d*t at h
    have hc := congrArg T h
    simp only [map_add,map_mul,base] at hc
    have hbd : fromPadics p b = fromPadics p d := by
      apply mul_right_cancel₀ unit.ne_zero
      linear_combination h - hc
    have hac : fromPadics p a = fromPadics p c := by simpa [hbd] using h
    exact Prod.ext (fromPadics_injective p hac) (fromPadics_injective p hbd)
  · intro x
    obtain ⟨j,hj⟩ := isUnit_iff_exists_inv.mp unit
    let b := (x-T x)*j
    have hb : b*(t-T t) = x-T x := by
      dsimp [b]; rw [mul_assoc,mul_comm j,hj,mul_one]
    have hbfix : T b = b := by
      apply mul_right_cancel₀ unit.ne_zero
      have hc := congrArg T hb
      simp only [map_mul,map_sub,hT] at hc
      linear_combination -hc - hb
    have hafix : T (x-b*t) = x-b*t := by
      rw [map_sub,map_mul,hbfix]; linear_combination hb
    obtain ⟨a, ha⟩ := fixed _ hafix
    obtain ⟨b', hb'⟩ := fixed _ hbfix
    exact ⟨(a,b'), by simp [ha,hb']⟩

instance padicAlgebra : Algebra ℤ_[p] (IntegralField p) := (fromPadics p).toAlgebra

/-- A linear equivalence certifies both spanning and independence of the integral basis. -/
def integralLinearEquiv : (ℤ_[p] × ℤ_[p]) ≃ₗ[ℤ_[p]] IntegralField p :=
  let t := (integral_coordinates p).choose
  let lin : (ℤ_[p] × ℤ_[p]) →ₗ[ℤ_[p]] IntegralField p := {
    toFun := fun ab => fromPadics p ab.1 + fromPadics p ab.2*t
    map_add' := by
      rintro ⟨a,b⟩ ⟨c,d⟩
      change fromPadics p (a+c)+fromPadics p (b+d)*t = _
      simp only [map_add]; ring
    map_smul' := by
      rintro z ⟨a,b⟩
      change fromPadics p (z*a)+fromPadics p (z*b)*t = fromPadics p z*(fromPadics p a+fromPadics p b*t)
      simp only [map_mul]; ring }
  LinearEquiv.ofBijective lin (integral_coordinates p).choose_spec

instance finite_integral : Module.Finite ℤ_[p] (IntegralField p) :=
  Module.Finite.of_surjective (integralLinearEquiv p).toLinearMap (integralLinearEquiv p).surjective

theorem integral_finrank : Module.finrank ℤ_[p] (IntegralField p) = 2 := by
  rw [← (integralLinearEquiv p).finrank_eq, Module.finrank_prod]; simp

theorem maximalIdeal_map :
    (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (IntegralField p)) =
      IsLocalRing.maximalIdeal (IntegralField p) := by
  rw [PadicInt.maximalIdeal_eq_span_p, maximalIdeal_eq, Ideal.map_span, Set.image_singleton, map_natCast]

instance local_padicAlgebra : IsLocalHom (algebraMap ℤ_[p] (IntegralField p)) :=
  ((IsLocalRing.local_hom_TFAE _).out 1 3 rfl rfl).mpr (maximalIdeal_map p).le

instance formally_unramified : Algebra.FormallyUnramified ℤ_[p] (IntegralField p) := by
  let : Finite (IsLocalRing.ResidueField (IntegralField p)) :=
    Finite.of_injective _ (residueFieldEquiv p).injective
  exact Algebra.FormallyUnramified.of_map_maximalIdeal (maximalIdeal_map p)

theorem ramification_index_one : (IsLocalRing.maximalIdeal (IntegralField p)).ramificationIdx ℤ_[p] = 1 :=
  Ideal.ramificationIdx_eq_one _ _

instance free_integral : Module.Free ℤ_[p] (IntegralField p) :=
  Module.Free.of_equiv (integralLinearEquiv p)

theorem finite_etale : Module.Finite ℤ_[p] (IntegralField p) ∧ Algebra.Etale ℤ_[p] (IntegralField p) :=
  by
    let : Algebra.FinitePresentation ℤ_[p] (IntegralField p) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact ⟨inferInstance, .of_formallyUnramified_of_flat⟩

abbrev LocalField := FractionRing (IntegralField p)

private theorem injective_to_fraction : Function.Injective (algebraMap ℤ_[p] (LocalField p)) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] (IntegralField p) (LocalField p)]
  exact (IsFractionRing.injective (IntegralField p) (LocalField p)).comp (fromPadics_injective p)

instance padicFieldAlgebra : Algebra ℚ_[p] (LocalField p) :=
  (IsFractionRing.lift (injective_to_fraction p)).toAlgebra

instance fraction_tower : IsScalarTower ℤ_[p] ℚ_[p] (LocalField p) :=
  IsScalarTower.of_algebraMap_eq (R := ℤ_[p]) (S := ℚ_[p]) (A := LocalField p) fun x => (IsFractionRing.lift_algebraMap (injective_to_fraction p) x).symm

theorem fraction_degree : Module.finrank ℚ_[p] (LocalField p) = 2 :=
  (IsFractionRing.finrank_eq ℤ_[p] ℚ_[p] (IntegralField p) (LocalField p)).trans (integral_finrank p)

theorem integral_closure : IsIntegralClosure (IntegralField p) ℤ_[p] (LocalField p) :=
  IsIntegralClosure.of_isIntegrallyClosedIn

theorem unramified_quadratic :
    Module.finrank ℚ_[p] (LocalField p) = 2 ∧
    (IsLocalRing.maximalIdeal (IntegralField p)).ramificationIdx ℤ_[p] = 1 ∧
    Nat.card (IsLocalRing.ResidueField (IntegralField p)) = p^2 := by
  refine ⟨fraction_degree p, ramification_index_one p, ?_⟩
  rw [Nat.card_congr (residueFieldEquiv p).toEquiv, FiniteField.natCard_extension, Nat.card_zmod]

end ZInQBlueprint.ResidueExtension
#print axioms ZInQBlueprint.ResidueExtension.integral_coordinates

#print axioms ZInQBlueprint.ResidueExtension.integralLinearEquiv
#print axioms ZInQBlueprint.ResidueExtension.finite_integral
#print axioms ZInQBlueprint.ResidueExtension.integral_finrank
#print axioms ZInQBlueprint.ResidueExtension.maximalIdeal_map
#print axioms ZInQBlueprint.ResidueExtension.formally_unramified
#print axioms ZInQBlueprint.ResidueExtension.ramification_index_one

#print axioms ZInQBlueprint.ResidueExtension.finite_etale
#print axioms ZInQBlueprint.ResidueExtension.integral_closure
#print axioms ZInQBlueprint.ResidueExtension.fraction_degree
#print axioms ZInQBlueprint.ResidueExtension.unramified_quadratic
