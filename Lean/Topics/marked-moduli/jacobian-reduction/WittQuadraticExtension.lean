import WittSquareClasses

/-! The integral and field degrees of the Witt extension containing the square roots. -/
namespace ZInQBlueprint.WittSquareClasses
noncomputable section
variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Finite k] [CharP k p]
local notation "R" => WittVector p k
local notation "E" => Extension p k
local notation "W" => WittVector p E

/-- A lift of any residue generator and 1 form a basis over the smaller Witt ring.
Conjugation gives the two coordinates since the conjugate lifts differ by a unit. -/
theorem coordinates : ∃ t : W, Function.Bijective
    (fun ab : R × R => extend p k ab.1 + extend p k ab.2 * t) := by
  classical
  let G := E ≃ₐ[k] E
  have card : Nat.card G = 2 := FiniteField.natCard_algEquiv_extension k p 2
  obtain ⟨g, hne, huniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp card
  have invol (z : E) : g (g z) = z := by
    have h2 : g*g = 1 := by simpa only [card, pow_two] using (pow_card_eq_one' (x := g))
    exact DFunLike.congr_fun h2 z
  let T : W →+* W := WittVector.map g.toRingHom
  have twice (x : W) : T (T x) = x := by ext i; exact invol _
  have base (a : R) : T (extend p k a) = extend p k a := by ext i; exact g.commutes _
  have inj : Function.Injective (extend p k) := WittVector.map_injective _ (algebraMap k E).injective
  have fixed (x : W) (hx : T x = x) : ∃ a : R, extend p k a = x := by
    have each (i : ℕ) : x.coeff i ∈ Set.range (algebraMap k E) := by
      apply (IsGalois.mem_range_algebraMap_iff_fixed (x.coeff i)).mpr
      intro σ
      by_cases h : σ = 1
      · simp [h]
      · rw [huniq σ h]
        exact congrArg (fun v : W => v.coeff i) hx
    choose b hb using each
    exact ⟨WittVector.mk p b, by ext i; exact hb i⟩
  have moved : ∃ r : E, g r ≠ r := by
    by_contra! h
    apply hne
    ext r
    exact h r
  obtain ⟨r, hr⟩ := moved
  obtain ⟨t, ht⟩ := WittVector.constantCoeff_surjective p r
  have unit : IsUnit (t - T t) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    change WittVector.constantCoeff (t - T t) ≠ 0
    rw [map_sub]
    change t.coeff 0 - g (t.coeff 0) ≠ 0
    change t.coeff 0 = r at ht
    exact sub_ne_zero.mpr (ht ▸ hr.symm)
  refine ⟨t, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    change extend p k a + extend p k b*t = extend p k c + extend p k d*t at h
    have conjugate := congrArg T h
    simp only [map_add, map_mul, base] at conjugate
    have eqb : extend p k b = extend p k d := by
      apply mul_right_cancel₀ unit.ne_zero
      linear_combination h - conjugate
    exact Prod.ext (inj (show extend p k a = extend p k c by simpa [eqb] using h)) (inj eqb)
  · intro x
    obtain ⟨j, hj⟩ := isUnit_iff_exists_inv.mp unit
    let b := (x - T x)*j
    have hb : b*(t - T t) = x - T x := by
      dsimp [b]
      rw [mul_assoc, mul_comm j, hj, mul_one]
    have bf : T b = b := by
      apply mul_right_cancel₀ unit.ne_zero
      have h := congrArg T hb
      simp only [map_mul, map_sub, twice] at h
      linear_combination -h - hb
    have af : T (x - b*t) = x - b*t := by
      rw [map_sub, map_mul, bf]
      linear_combination hb
    obtain ⟨a, ha⟩ := fixed _ af
    obtain ⟨b', hb'⟩ := fixed _ bf
    exact ⟨(a, b'), by simp [ha, hb']⟩

def coordinateEquiv : (R × R) ≃ₗ[R] W :=
  let t := (coordinates p k).choose
  let f : (R × R) →ₗ[R] W := {
    toFun := fun ab => extend p k ab.1 + extend p k ab.2*t
    map_add' := by
      rintro ⟨a,b⟩ ⟨c,d⟩
      change extend p k (a+c) + extend p k (b+d)*t = _
      simp only [map_add]
      ring
    map_smul' := by
      rintro z ⟨a,b⟩
      change extend p k (z*a) + extend p k (z*b)*t = extend p k z*(extend p k a + extend p k b*t)
      simp only [map_mul]
      ring }
  LinearEquiv.ofBijective f (coordinates p k).choose_spec

instance finite : Module.Finite R W :=
  Module.Finite.of_surjective (coordinateEquiv p k).toLinearMap (coordinateEquiv p k).surjective

instance free : Module.Free R W := Module.Free.of_equiv (coordinateEquiv p k)

theorem finite_etale : Algebra.Etale R W ∧ Module.finrank R W = 2 := by
  have m : (IsLocalRing.maximalIdeal R).map (algebraMap R W) = IsLocalRing.maximalIdeal W := by
    rw [(WittVector.irreducible p (k := k)).maximalIdeal_eq,
      (WittVector.irreducible p (k := E)).maximalIdeal_eq, Ideal.map_span, Set.image_singleton, map_natCast]
  let : IsLocalHom (algebraMap R W) := ((IsLocalRing.local_hom_TFAE _).out 1 3 rfl rfl).mpr m.le
  let : Finite (IsLocalRing.ResidueField W) := Finite.of_injective _ (residueIso p k).injective
  let : Algebra.FormallyUnramified R W := Algebra.FormallyUnramified.of_map_maximalIdeal m
  let : Algebra.FinitePresentation R W := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨.of_formallyUnramified_of_flat, by rw [← (coordinateEquiv p k).finrank_eq, Module.finrank_prod]; simp⟩

end
end ZInQBlueprint.WittSquareClasses
#print axioms ZInQBlueprint.WittSquareClasses.coordinates
#print axioms ZInQBlueprint.WittSquareClasses.coordinateEquiv
#print axioms ZInQBlueprint.WittSquareClasses.finite_etale
