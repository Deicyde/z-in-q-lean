import BoundedFromGenus
import FinitePolynomial
import QualitativeMultiplication
import QualitativePrecision

/-! Existence of a polynomial defining the integers from a uniform six-contact
height estimate and the congruent-number rank criterion. -/

namespace ZOverQ.Qualitative

open ZInQ ZInQ.Syntax MvPolynomial

/-- One integer polynomial, with one distinguished rational coordinate and a
finite tuple of rational witnesses, defines the ordinary integers. -/
def IntegerPolynomial : Prop :=
  ∃ k : ℕ, ∃ p : MvPolynomial (Fin (k + 1)) ℤ, ∀ t : ℚ,
    (∃ w : Fin k → ℚ, eval₂ (Int.castRingHom ℚ) (Fin.cons t w) p = 0) ↔
      ∃ z : ℤ, (z : ℚ) = t

private abbrev Codes := Fin 3 × Fin 5
private abbrev Visible := Unit ⊕ Codes

private def code (i : Fin 3) (j : Fin 5) : Visible := .inr (i,j)

private def two (i j : Fin 3) : Fin 10 → Visible := Fin.append (code i) (code j)
private def three (i j : Fin 3) : Fin 11 → Visible := Fin.append (two i j) ![.inl ()]

private theorem eval_two (a : Visible → ℚ) (i j : Fin 3) :
    a ∘ two i j = Fin.append (a ∘ code i) (a ∘ code j) := by
  funext k
  fin_cases k <;> rfl

private theorem eval_three (a : Visible → ℚ) (i j : Fin 3) :
    a ∘ three i j = Fin.append (Fin.append (a ∘ code i) (a ∘ code j)) ![a (.inl ())] := by
  funext k
  fin_cases k <;> rfl

private noncomputable abbrev test (T : ℤ) :=
  valueTestTemplate specConstructors FixedConst.cstar.value FixedConst.ell.value T

private noncomputable abbrev scale (m : ℕ) := scalarTemplate specConstructors (m : ℤ)

private def Joint (T : ℤ) (m : ℕ) (a : Visible → ℚ) : Prop :=
  (test T).Rel (Fin.append (Fin.append (a ∘ code 0) (a ∘ code 1)) ![a (.inl ())]) ∧
  (scale m).Rel (Fin.append (a ∘ code 1) (a ∘ code 2)) ∧
    CloseAt T (a ∘ code 0) (a ∘ code 2) (a (.inl ()))

private theorem joint_polynomial (T : ℤ) (m : ℕ) : PolynomialRelation (Joint T m) := by
  let τ := getEx (precisionLibrary T) 2
  have hclose : PolynomialRelation (fun a : Visible → ℚ =>
      CloseAt T (a ∘ code 0) (a ∘ code 2) (a (.inl ()))) := by
    apply (PolynomialRelation.template τ (fun k => three 0 2 (Fin.cast (closeParams T) k))).congr
    intro a
    rw [closeAt_iff_rel]
    apply Iff.of_eq
    apply congrArg τ.Rel
    funext k
    exact congrFun (eval_three a 0 2) (Fin.cast (closeParams T) k)
  have hscale := (PolynomialRelation.template (scale m) (two 1 2)).congr
    (fun a => (congrArg (scale m).Rel (eval_two a 1 2)).to_iff)
  have htest := (PolynomialRelation.template (test T) (three 0 1)).congr
    (fun a => (congrArg (test T).Rel (eval_three a 0 1)).to_iff)
  exact htest.conj (hscale.conj hclose)

private def pack (N K K' : Fin 5 → ℚ) (c : Codes) : ℚ :=
  ![N, K, K'] c.1 c.2

private theorem off_contacts {m : ℕ} (hm : 1 ≤ m) (hH : UniformHeight (m : ℝ))
    (hP : PoleCompleteness) (q : ℚ) :
    (∃ u : Codes → ℚ, Joint (guardCutoff m) m (Sum.elim (fun _ => q) u)) ↔
      ∃ z : ℤ, (z : ℚ) = q ∧ q ∉ contactSet := by
  have hM := multiplication_exact hm hH hP
  constructor
  · rintro ⟨u, ht, hs, hc⟩
    obtain ⟨z, _, hq, hz⟩ := (main_iff hM hP hm hH (fun j => u (0,j)) q).1
      ⟨fun j => u (1,j), fun j => u (2,j), ht, hs, hc⟩
    exact ⟨z, hq.symm, hq ▸ hz⟩
  · rintro ⟨z, rfl, hz⟩
    obtain ⟨K, K', ht, hs, hc⟩ := (main_iff hM hP hm hH (iota z) (z : ℚ)).2 ⟨z, rfl, rfl, hz⟩
    exact ⟨pack (iota z) K K', ht, hs, hc⟩

private noncomputable def exceptional {k : ℕ} : MvPolynomial (Fin (k + 1)) ℤ :=
  X 0 * (X 0 + 15) * (X 0 + 20) * (X 0 + 24) * (X 0 + 30) * (X 0 + 60)

private theorem exceptional_iff {k : ℕ} (q : ℚ) (w : Fin k → ℚ) :
    eval₂ (Int.castRingHom ℚ) (Fin.cons q w) exceptional = 0 ↔ q ∈ contactSet := by
  simp only [exceptional, eval₂_mul, eval₂_add, eval₂_X, eval₂_ofNat, Fin.cons_zero,
    mul_eq_zero, contactSet, Finset.mem_insert, Finset.mem_singleton, add_eq_zero_iff_eq_neg]
  tauto

/-- The coefficients and witness count may depend on the uniform height constant. -/
theorem integer_polynomial_of_height_and_rank {C : ℝ} (height : UniformHeight C)
    (rank : RouteK.Rank.CertifiedRankTYZClRk) : IntegerPolynomial := by
  obtain ⟨m, hm, hH⟩ := exists_integer_height height
  have hP := pole_of_class_sum rank
  obtain ⟨k, P, hPdef⟩ := (joint_polynomial (guardCutoff m) m).project
  refine ⟨k, exceptional * P, ?_⟩
  intro t
  have main := (hPdef t).trans (off_contacts hm hH hP t)
  constructor
  · rintro ⟨w, hw⟩
    rw [eval₂_mul, mul_eq_zero, exceptional_iff] at hw
    rcases hw with hc | h
    · obtain ⟨z, hz, _⟩ := Assembly.contactSet_int hc
      exact ⟨z, hz⟩
    · obtain ⟨z, hz, _⟩ := main.1 ⟨w, h⟩
      exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    by_cases hc : t ∈ contactSet
    · exact ⟨0, by rw [eval₂_mul, (exceptional_iff t _).2 hc, zero_mul]⟩
    · obtain ⟨w, hw⟩ := main.2 ⟨z, hz, hc⟩
      exact ⟨w, by rw [eval₂_mul, hw, mul_zero]⟩

/-- The analytic inputs are Tian's odd genus criterion and the positive-rank
consequence of a simple central zero for rational elliptic curves. -/
theorem integer_polynomial_of_uniform_height {C : ℝ} (height : UniformHeight C)
    (tian : ZInQBlueprint.OriginalRank.PublishedGenusRows.PublishedTian47)
    (grossZagier : ZOverQ.Bounded.SimpleZeroRank) : IntegerPolynomial :=
  integer_polynomial_of_height_and_rank height (ZOverQ.Bounded.certified_rank_from_tian tian grossZagier)

end ZOverQ.Qualitative

#print axioms ZOverQ.Qualitative.integer_polynomial_of_height_and_rank
#print axioms ZOverQ.Qualitative.integer_polynomial_of_uniform_height
