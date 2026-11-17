import LocalKummerFibre

namespace Sun28.LocalOrbit
open Sun28.SelmerRealization
variable {K : Type*} [Field K] [CharZero K]

/-- On the pencil l=ac, translation by (l,0) exchanges the two
normalized labels a and c. This homogeneous linear map has no exceptional
denominator or choice of square root. -/
theorem exchange {l : ℕ} {a c : ℤ} (dec : (l:ℤ)=a*c) (an : a≠0) (ln : l≠0)
    (h : Cover K l a 1) : Cover K l c 1 := by
  obtain ⟨X,Y,Z,T,ok,E,F⟩ := h
  have A : (a:K)≠0 := Int.cast_ne_zero.mpr an
  have L : (l:K)≠0 := Nat.cast_ne_zero.mpr ln
  have h2 : (2:K)≠0 := by norm_num
  have H : (l:K)=(a:K)*(c:K) := by exact_mod_cast dec
  simp only [Int.cast_one,mul_one,one_mul] at E F
  refine ⟨(a:K)*Z,2*(l:K)*T,2*(a:K)*X,Y,?_,?_,?_⟩
  · rcases ok with hx|hy|hz|ht
    · exact Or.inr (Or.inr (Or.inl (mul_ne_zero (mul_ne_zero h2 A) hx)))
    · exact Or.inr (Or.inr (Or.inr hy))
    · exact Or.inl (mul_ne_zero A hz)
    · exact Or.inr (Or.inl (mul_ne_zero (mul_ne_zero h2 L) ht))
  · simp only [Int.cast_one,mul_one,one_mul]
    rw [H] at E F ⊢
    linear_combination ((a:K)*c)*(E+F)
  · simp only [Int.cast_one,mul_one]
    rw [H] at E F ⊢
    linear_combination ((a:K)*c)*(3*E-F)

theorem exchange_iff {l : ℕ} {a c : ℤ} (dec : (l:ℤ)=a*c) (ln : l≠0) :
    Cover K l a 1 ↔ Cover K l c 1 := by
  have non : a*c≠0 := dec ▸ (by exact_mod_cast ln : (l:ℤ)≠0)
  rw [mul_ne_zero_iff] at non
  exact ⟨exchange dec non.1 ln,exchange (dec.trans (mul_comm _ _)) non.2 ln⟩

/-- Translation by the root (-3l,0), in the homogeneous covering
coordinates. Its image has the signed labels (3a,-l). -/
theorem signed_translate {l : ℕ} {a : ℤ} (an : a≠0) (ln : l≠0)
    (h : Cover K l a 1) : Cover K l (3*a) (-(l:ℤ)) := by
  obtain ⟨X,Y,Z,T,ok,E,F⟩ := h
  have A : (a:K)≠0 := Int.cast_ne_zero.mpr an
  have L : (l:K)≠0 := Nat.cast_ne_zero.mpr ln
  have h2 : (2:K)≠0 := by norm_num
  simp only [Int.cast_one,mul_one,one_mul] at E F
  refine ⟨Y,2*(a:K)*X,2*(l:K)*T,(a:K)*Z,?_,?_,?_⟩
  · rcases ok with hx|hy|hz|ht
    · exact Or.inr (Or.inl (mul_ne_zero (mul_ne_zero h2 A) hx))
    · exact Or.inl hy
    · exact Or.inr (Or.inr (Or.inr (mul_ne_zero A hz)))
    · exact Or.inr (Or.inr (Or.inl (mul_ne_zero (mul_ne_zero h2 L) ht)))
  · push_cast
    linear_combination ((a:K)*l)*(3*E-F)
  · push_cast
    linear_combination (-3*(a:K)*l)*(E+F)

end Sun28.LocalOrbit
#print axioms Sun28.LocalOrbit.exchange
#print axioms Sun28.LocalOrbit.exchange_iff
#print axioms Sun28.LocalOrbit.signed_translate
