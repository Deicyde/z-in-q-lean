import SimultaneousContacts
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! A parameter-dependent choice among the twenty triples cannot remove all even-contact poles. -/
namespace ZInQBlueprint.ContactDescent

def legendreJ (l : ℚ) := 256*(1-l+l^2)^3/(l^2*(1-l)^2)

/-- Normalized rational cross-ratio of u and three distinct marks. -/
def ratio (u : ℕ) (i j k : Fin 6) : ℚ :=
  ((u+mark i : ℕ):ℚ) / ((u+mark k : ℕ):ℚ) *
    (((mark j:ℚ)-mark k)/((mark j:ℚ)-mark i))

private theorem val_mark_diff (p : ℕ) [Fact p.Prime] (hp : 60 < p)
    {i j : Fin 6} (h : i ≠ j) : padicValRat p ((mark i:ℚ)-mark j)=0 := by
  let z := (mark i:ℤ) - mark j
  have hz : z ≠ 0 := by
    intro he
    apply h
    apply mark_injective
    exact_mod_cast (sub_eq_zero.mp he : (mark i:ℤ) = (mark j:ℤ))
  have hs : z.natAbs < p := by
    have hi := mark_bound i
    have hj := mark_bound j
    dsimp [z]
    omega
  have hh : ¬ (p:ℤ) ∣ z := by
    intro h
    have hd : p ∣ z.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr h
    exact (not_le_of_gt hs) (Nat.le_of_dvd (Int.natAbs_pos.mpr hz) hd)
  have h' : ((z:ℤ):ℚ)=(mark i:ℚ)-mark j := by simp [z]
  rw [← h',padicValRat.of_int,padicValInt.eq_zero_of_not_dvd hh]; norm_num

theorem legendre_pole (p : ℕ) [Fact p.Prime] (hp : 60 < p)
    (l : ℚ) (hl : padicValRat p l = 2) : padicValRat p (legendreJ l) = -4 := by
  have hl0 : l ≠ 0 := by intro h; simp [h] at hl
  have h1 : 1-l ≠ 0 := by intro h; have hh := sub_eq_zero.mp h; simp [← hh] at hl
  have h1v : padicValRat p (1-l) = 0 := by
    rw [sub_eq_add_neg] at h1 ⊢
    rw [padicValRat.add_eq_min (by exact h1) (by norm_num) (neg_ne_zero.mpr hl0)
      (by simp [hl])]
    simp [hl]
  have hf : 1-l+l^2 ≠ 0 := by nlinarith [sq_nonneg (2*l-1)]
  have hv : padicValRat p (1-l+l^2) = 0 := by
    rw [padicValRat.add_eq_min hf h1 (pow_ne_zero _ hl0) (by simp [h1v,hl])]
    simp [h1v,hl]
  have h256 : padicValRat p 256 = 0 := by
    have h : ¬p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    have h2 : padicValRat p (2:ℚ) = 0 := by
      change padicValRat p ((2:ℕ):ℚ) = 0
      rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd h]; norm_num
    rw [show (256:ℚ)=(2:ℚ)^8 by norm_num,padicValRat.pow,h2]; norm_num
  rw [legendreJ,padicValRat.div (mul_ne_zero (by norm_num) (pow_ne_zero _ hf))
        (mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ h1)),
      padicValRat.mul (by norm_num) (pow_ne_zero _ hf),
      padicValRat.mul (pow_ne_zero _ hl0) (pow_ne_zero _ h1)]
  simp [h256,hv,hl,h1v]

/-- At a prime contacting the first mark precisely twice, every Legendre triple
containing it as first entry has negative j-valuation. The other two marks are arbitrary. -/
theorem triple_pole {p u : ℕ} [hp' : Fact p.Prime] (hp : 60 < p) (hu : 0 < u)
    {i j k : Fin 6} (hji : j ≠ i) (hjk : j ≠ k)
    (hc : (u+mark i).factorization p = 2) (hk : ¬ p ∣ u+mark k) :
    padicValRat p (legendreJ (ratio u i j k)) = -4 := by
  apply legendre_pole p hp
  have hui : ((u+mark i : ℕ):ℚ) ≠ 0 := by positivity
  have huk : ((u+mark k : ℕ):ℚ) ≠ 0 := by positivity
  have diff {a b : Fin 6} (h : a ≠ b) : (mark a:ℚ)-mark b ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast mark_injective.ne h
  have vi : padicValRat p ((u+mark i : ℕ):ℚ) = 2 := by
    rw [padicValRat.of_nat,← Nat.factorization_def _ hp'.out,hc]; norm_num
  have vk : padicValRat p ((u+mark k : ℕ):ℚ) = 0 := by
    rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd hk]; norm_num
  rw [ratio,padicValRat.mul (div_ne_zero hui huk) (div_ne_zero (diff hjk) (diff hji)),
      padicValRat.div hui huk,padicValRat.div (diff hjk) (diff hji),
      val_mark_diff p hp hjk,val_mark_diff p hp hji,vi,vk]
  norm_num

/-- At arbitrarily large integer inputs *every* choice of three distinct marks has a
prime of even contact outside the chosen bound where its Legendre j has a literal pole. -/
theorem all_triples_obstructed (bound H : ℕ) :
    ∃ (p : Fin 6 → ℕ) (u : ℕ), H < u ∧ Function.Injective p ∧
      ∀ i, (p i).Prime ∧ max 60 bound < p i ∧
        (∀ j : Fin 6, (u+mark j).factorization (p i) = if j=i then 2 else 0) ∧
        ∀ j k : Fin 6, j ≠ i → j ≠ k → k ≠ i →
          padicValRat (p i) (legendreJ (ratio u i j k)) = -4 := by
  obtain ⟨p,u,hi,hu,h⟩ := arbitrarily_large_private_contacts bound H
  refine ⟨p,u,hu,hi,?_⟩
  intro i
  obtain ⟨hp,hb,hc,ho⟩ := h i
  refine ⟨hp,hb,?_,?_⟩
  · intro j
    by_cases he : j=i
    · simpa [he] using hc
    · simpa [he] using Nat.factorization_eq_zero_of_not_dvd (ho j he)
  · intro j k hji hjk hki
    let : Fact (p i).Prime := ⟨hp⟩
    exact triple_pole ((le_max_left ..).trans_lt hb) (by omega) hji hjk hc (ho k hki)

end ZInQBlueprint.ContactDescent
#print axioms ZInQBlueprint.ContactDescent.legendre_pole
#print axioms ZInQBlueprint.ContactDescent.triple_pole
#print axioms ZInQBlueprint.ContactDescent.all_triples_obstructed
