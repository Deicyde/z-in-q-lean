import ResultantGuards

/-! Recover rational tuples from roots of the literal resultant polynomial. -/
open Polynomial Finset
namespace ZInQBlueprint.SunResultant.ParamTower
open ZInQBlueprint.SunTower
noncomputable section
variable {R : Type*} [CommRing R]
local notation "Ω" => AlgebraicClosure ℚ
local instance : DecidableEq Ω := Classical.decEq _

/-- Transport equations along an injective coefficient-preserving field homomorphism. -/
theorem satisfies_hom {K L : Type*} [Field K] [Field L] (φ : R →+* K) (η : K →+* L)
    {n : ℕ} (T : ParamTower R n) (x : Fin n → K) :
    Satisfies (η.comp φ) T (fun i => η (x i)) ↔ Satisfies φ T x := by
  induction T with
  | base => rfl
  | @adjoin n T f hf ih =>
    have c : η.comp (MvPolynomial.eval₂Hom φ (Fin.tail x)) =
        MvPolynomial.eval₂Hom (η.comp φ) (fun i => η (Fin.tail x i)) := by
      apply RingHom.ext
      intro g
      exact MvPolynomial.map_eval₂Hom φ (Fin.tail x) η g
    change (Satisfies (η.comp φ) T (fun i => η (Fin.tail x i)) ∧
      (f.map (MvPolynomial.eval₂Hom (η.comp φ) (fun i => η (Fin.tail x i)))).eval (η (x 0)) = 0) ↔ _
    rw [← c,← Polynomial.map_map,eval_map_apply,map_eq_zero_iff _ η.injective]
    exact and_congr (ih _) Iff.rfl

/-- A specified rational root of a separating locator lifts to a rational tuple with exactly that value. -/
theorem rational_locator_at {n : ℕ} (T : ParamTower R n) (φ : R →+* ℚ) {b : ℕ}
    (hi : Set.InjOn (separator (b:AlgebraicClosure ℚ))
        ((rootTuples ((algebraMap ℚ (AlgebraicClosure ℚ)).comp φ) T).toFinset : Set (Fin n → AlgebraicClosure ℚ)))
    (z : ℚ) :
    ((imagePolynomial T (linearForm R n b)).map φ).IsRoot z ↔
      ∃ x : Fin n → ℚ, Satisfies φ T x ∧ separator (b : ℚ) x = z := by
  classical
  let L := AlgebraicClosure ℚ
  let ι : ℚ →+* L := algebraMap ℚ L
  let ρ := ι.comp φ
  let S := (rootTuples ρ T).toFinset
  have stable : Stable ℚ S := by
    intro σ x hx
    have hh := (mem_rootTuples ρ T x).mp (Multiset.mem_toFinset.mp hx)
    have e : σ.toRingHom.comp ρ = ρ := by
      apply RingHom.ext
      intro a
      exact σ.commutes (φ a)
    exact Multiset.mem_toFinset.mpr ((mem_rootTuples ρ T _).mpr (e ▸ (satisfies_hom ρ σ.toRingHom T x).mpr hh))
  let P := imagePolynomial T (linearForm R n b)
  have he (z : ℚ) : (P.map φ).IsRoot z ↔ (P.map ρ).IsRoot (ι z) := by
    change (P.map φ).eval z = 0 ↔ (P.map (ι.comp φ)).eval (ι z) = 0
    rw [← Polynomial.map_map,eval_map_apply,map_eq_zero_iff _ ι.injective]
  have eq (x : Fin n → L) : MvPolynomial.eval₂Hom ρ x (linearForm R n b) = separator (b:L) x := by
    simp [linearForm,separator]
  constructor
  · intro hz
    obtain ⟨x,hx,hv⟩ := (imagePolynomial_isRoot_iff T _ ρ (ι z)).mp ((he z).mp hz)
    have hs : x ∈ S := Multiset.mem_toFinset.mpr ((mem_rootTuples ρ T x).mpr hx)
    obtain ⟨y,hy⟩ := rational_tuple_of_separating stable hi hs z ((eq x).symm.trans hv)
    refine ⟨y,(satisfies_hom φ ι T y).mp (hy ▸ hx),ι.injective ?_⟩
    calc
      ι (separator (b:ℚ) y) = separator (b:L) (fun i => ι (y i)) := by simp [separator]
      _ = ι z := by rw [hy,← eq x,hv]
  · rintro ⟨y,hy,rfl⟩
    refine (he _).mpr ((imagePolynomial_isRoot_iff T _ ρ _).mpr ⟨_,(satisfies_hom φ ι T y).mpr hy,?_⟩)
    rw [eq]
    simp [separator]

/-- The projected polynomial has a rational root precisely when the tower has a rational tuple. -/
theorem rational_locator {n : ℕ} (T : ParamTower R n) (φ : R →+* ℚ) {b : ℕ}
    (hi : Set.InjOn (separator (b:AlgebraicClosure ℚ))
        ((rootTuples ((algebraMap ℚ (AlgebraicClosure ℚ)).comp φ) T).toFinset : Set (Fin n → AlgebraicClosure ℚ))) :
    (∃ z : ℚ, ((imagePolynomial T (linearForm R n b)).map φ).IsRoot z) ↔
      ∃ x : Fin n → ℚ, Satisfies φ T x := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨x,hx,_⟩ := (rational_locator_at T φ hi z).mp hz
    exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨_,(rational_locator_at T φ hi _).mpr ⟨x,hx,rfl⟩⟩

/-- Search a fixed list of integer polynomials indexed by b. At each rational specialization
at least one of them has the exact rational-tuple equivalence. -/
theorem exists_rational_locator {n : ℕ} (T : ParamTower R n) (φ : R →+* ℚ) :
    ∃ b : ℕ, b ≤ T.degreeProduct.choose 2*(n-1) ∧
      ((∃ z : ℚ, ((imagePolynomial T (linearForm R n b)).map φ).IsRoot z) ↔
        ∃ x : Fin n → ℚ, Satisfies φ T x) := by
  classical
  let ρ := (algebraMap ℚ (AlgebraicClosure ℚ)).comp φ
  let M := rootTuples ρ T
  obtain ⟨b,hb,hi⟩ := exists_bounded_separator M.toFinset
  have h : M.toFinset.card ≤ T.degreeProduct := (Multiset.toFinset_card_le _).trans_eq (card_rootTuples ρ T)
  exact ⟨b,hb.trans (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 h)),rational_locator T φ hi⟩

end
end ZInQBlueprint.SunResultant.ParamTower
#print axioms ZInQBlueprint.SunResultant.ParamTower.satisfies_hom
#print axioms ZInQBlueprint.SunResultant.ParamTower.rational_locator_at
#print axioms ZInQBlueprint.SunResultant.ParamTower.rational_locator
#print axioms ZInQBlueprint.SunResultant.ParamTower.exists_rational_locator
