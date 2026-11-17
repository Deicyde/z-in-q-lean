import TriangularRootSet

/-! Equations and inequations in the tuple may be imposed before taking the geometric product. -/
open Polynomial Finset
namespace ZInQBlueprint.SunTower.Tower
noncomputable section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- Tests on the complete tuple, after clearing any previously guarded denominators. -/
def Tests (eqs neqs : Finset (MvPolynomial (Fin n) K)) (x : Fin n → L) : Prop :=
  (∀ f ∈ eqs, MvPolynomial.aeval x f = 0) ∧ (∀ f ∈ neqs, MvPolynomial.aeval x f ≠ 0)

theorem tests_map {M : Type*} [Field M] [Algebra K M] (φ : L →ₐ[K] M)
    (eqs neqs : Finset (MvPolynomial (Fin n) K)) (x : Fin n → L) :
    Tests eqs neqs (fun i => φ (x i)) ↔ Tests eqs neqs x := by
  have hz (f : MvPolynomial (Fin n) K) :
      MvPolynomial.aeval (fun i => φ (x i)) f = 0 ↔ MvPolynomial.aeval x f = 0 := by
    rw [← MvPolynomial.comp_aeval_apply, map_eq_zero_iff φ φ.injective]
  simp only [Tests,ne_eq,hz]

def accepted (L : Type*) [Field L] [Algebra K L] (T : Tower K n)
    (eqs neqs : Finset (MvPolynomial (Fin n) K)) : Finset (Fin n → L) := by
  classical
  exact (solutions L T).filter (Tests eqs neqs)

theorem mem_accepted (T : Tower K n) (eqs neqs : Finset (MvPolynomial (Fin n) K))
    (x : Fin n → L) : x ∈ accepted L T eqs neqs ↔ Satisfies T x ∧ Tests eqs neqs x := by
  classical
  simp [accepted,mem_solutions_iff]

/-- The fiberwise monic projection handles successive, potentially nonseparable adjoining
steps and all polynomial equality and nonvanishing tests without additional witnesses. -/
theorem exists_filtered_projection (T : Tower ℚ n) (eqs neqs : Finset (MvPolynomial (Fin n) ℚ)) :
    ∃ (b : ℕ) (p : ℚ[X]), b ≤ T.degreeBound.choose 2*(n-1) ∧ p.Monic ∧
      p.natDegree ≤ T.degreeBound ∧
      p.map (algebraMap ℚ (AlgebraicClosure ℚ)) = projection (accepted (AlgebraicClosure ℚ) T eqs neqs) b ∧
      ((∃ z : ℚ, p.IsRoot z) ↔ ∃ x : Fin n → ℚ, Satisfies T x ∧ Tests eqs neqs x) := by
  classical
  let L := AlgebraicClosure ℚ
  have h (x : Fin n → L) (σ : L ≃ₐ[ℚ] L) :
      (fun i => σ (x i)) ∈ accepted L T eqs neqs ↔ x ∈ accepted L T eqs neqs := by
    rw [mem_accepted,mem_accepted]
    exact and_congr (satisfies_map σ.toAlgHom T x) (tests_map σ.toAlgHom eqs neqs x)
  have stable : Stable ℚ (accepted L T eqs neqs) := fun σ x hx => (h x σ).mpr hx
  obtain ⟨b,p,hb,hm,hd,hp,he⟩ := exists_rational_root_iff stable
  have hs : (accepted L T eqs neqs).card ≤ T.degreeBound :=
    (Finset.card_filter_le ..).trans (card_solutions_le L T)
  refine ⟨b,p,hb.trans (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hs)),hm,hd.le.trans hs,hp,he.trans ?_⟩
  apply exists_congr
  intro x
  rw [mem_accepted]
  exact and_congr (satisfies_map (Algebra.ofId ℚ L) T x) (tests_map (Algebra.ofId ℚ L) eqs neqs x)

/-- The 26 auxiliary scalars and the 18 quartic and 8 quadratic degree bounds in Sun's
Proposition 10.1 give this uniform finite search range at each fixed rational input. -/
theorem sun_projection_budget (T : Tower ℚ 26) (hdegree : T.degreeBound ≤ 4^18*2^8)
    (eqs neqs : Finset (MvPolynomial (Fin 26) ℚ)) :
    ∃ (b : ℕ) (p : ℚ[X]), b ≤ (2^44).choose 2*25 ∧ p.Monic ∧ p.natDegree ≤ 2^44 ∧
      p.map (algebraMap ℚ (AlgebraicClosure ℚ)) = projection (accepted (AlgebraicClosure ℚ) T eqs neqs) b ∧
      ((∃ z : ℚ, p.IsRoot z) ↔ ∃ x : Fin 26 → ℚ, Satisfies T x ∧ Tests eqs neqs x) := by
  obtain ⟨b,p,hb,hm,hd,hp,he⟩ := exists_filtered_projection T eqs neqs
  have h : T.degreeBound ≤ 2^44 := hdegree.trans_eq (by norm_num)
  exact ⟨b,p,hb.trans (Nat.mul_le_mul_right 25 (Nat.choose_le_choose 2 h)),hm,hd.trans h,hp,he⟩

end
end ZInQBlueprint.SunTower.Tower
#print axioms ZInQBlueprint.SunTower.Tower.tests_map
#print axioms ZInQBlueprint.SunTower.Tower.mem_accepted
#print axioms ZInQBlueprint.SunTower.Tower.exists_filtered_projection
#print axioms ZInQBlueprint.SunTower.Tower.sun_projection_budget
