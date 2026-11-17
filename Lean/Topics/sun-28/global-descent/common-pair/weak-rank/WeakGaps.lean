import WeakRationalClasses

namespace Sun28.WeakRank
open Sun28.SelmerRealization Sun28.LocalOrbit
noncomputable section

private theorem signed_back {K : Type*} [Field K] [CharZero K] {l : ℕ} {a : ℤ} (an : a≠0) (ln : l≠0)
    (H : Cover K l (3*a) (-(l:ℤ))) : Cover K l a 1 := by
  obtain ⟨X,Y,Z,T,ok,E,F⟩ := H
  have A : (a:K)≠0 := Int.cast_ne_zero.mpr an
  have L : (l:K)≠0 := Nat.cast_ne_zero.mpr ln
  have t : (2:K)≠0 := by norm_num
  refine ⟨(l:K)*Y,2*(a:K)*l*X,2*(l:K)*T,(a:K)*Z,?_,?_,?_⟩
  · rcases ok with h|h|h|h
    · exact Or.inr (Or.inl (mul_ne_zero (mul_ne_zero (mul_ne_zero t A) L) h))
    · exact Or.inl (mul_ne_zero L h)
    · exact Or.inr (Or.inr (Or.inr (mul_ne_zero A h)))
    · exact Or.inr (Or.inr (Or.inl (mul_ne_zero (mul_ne_zero t L) h)))
  · push_cast at E F ⊢
    linear_combination (a:K)*l*E/1 - (a:K)*l*F/3
  · push_cast at E F ⊢
    linear_combination -(a:K)*l*E - (a:K)*l*F

private def four (b k l : ℕ) : Fin 4 → ℤ × ℤ :=
  ![((b:ℤ),1),((k:ℤ),1),(3*(b:ℤ),-(l:ℤ)),(3*(k:ℤ),-(l:ℤ))]

/-- A forbidden projective covering has four distinct everywhere-local,
globally insoluble labels in its orbit under rational two-torsion. -/
theorem missing_four {b k l : ℕ} (bb : 1<b) (kb : 1<k) (eq : l=b*k)
    (sf : Squarefree (3*l)) (loc : ((b:ℤ),1)∈localClasses l)
    (missing : ¬Cover ℚ l b 1) :
    ∃ g : Fin 4 → ℤ×ℤ, Function.Injective g ∧
      ∀ i, g i∈localClasses l ∧ ¬Cover ℚ l (g i).1 (g i).2 := by
  have lp : 0<l := eq ▸ Nat.mul_pos (by omega) (by omega)
  have L : l≠0 := lp.ne'
  have B : (b:ℤ)≠0 := by omega
  have K : (k:ℤ)≠0 := by omega
  have fac : (l:ℤ)=(b:ℤ)*k := by exact_mod_cast eq
  have sl : Squarefree l := sf.squarefree_of_dvd (dvd_mul_left l 3)
  have sbk := Nat.squarefree_mul_iff.mp (eq ▸ sl)
  have ne : b≠k := by
    rintro rfl
    have cop := sbk.1
    have one : b=1 := by simpa [Nat.Coprime] using cop
    omega
  have zl : Squarefree (-(l:ℤ)) := by
    simpa only [←Int.squarefree_natAbs,Int.natAbs_neg,Int.natAbs_natCast] using sl
  have sfB : Squarefree (3*(b:ℤ)) := by
    have dd : 3*b ∣ 3*l := Nat.mul_dvd_mul_left _ (eq ▸ dvd_mul_right b k)
    exact_mod_cast (Int.squarefree_natCast.mpr (sf.squarefree_of_dvd dd))
  have sfK : Squarefree (3*(k:ℤ)) := by
    have dd : 3*k ∣ 3*l := Nat.mul_dvd_mul_left _ (eq ▸ dvd_mul_left k b)
    exact_mod_cast (Int.squarefree_natCast.mpr (sf.squarefree_of_dvd dd))
  have atK {F : Type} [Field F] [CharZero F] : Cover F l b 1 ↔ Cover F l k 1 := exchange_iff fac L
  have localK : ((k:ℤ),1)∈localClasses l :=
    ⟨Int.squarefree_natCast.mpr sbk.2.2,squarefree_one,atK.mp loc.2.2.1,fun p _=>atK.mp (loc.2.2.2 p)⟩
  have noK : ¬Cover ℚ l k 1 := fun h=>missing (atK.mpr h)
  have negB : (3*(b:ℤ),-(l:ℤ))∈localClasses l :=
    ⟨sfB,zl,signed_translate B L loc.2.2.1,fun p _=>signed_translate B L (loc.2.2.2 p)⟩
  have negK : (3*(k:ℤ),-(l:ℤ))∈localClasses l :=
    ⟨sfK,zl,signed_translate K L localK.2.2.1,fun p _=>signed_translate K L (localK.2.2.2 p)⟩
  refine ⟨four b k l,?_,?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp [four] at h ⊢ <;> omega
  · intro i
    fin_cases i
    · exact ⟨loc,missing⟩
    · exact ⟨localK,noK⟩
    · exact ⟨negB,fun h=>missing (signed_back B L h)⟩
    · exact ⟨negK,fun h=>noK (signed_back K L h)⟩

end
end Sun28.WeakRank
#print axioms Sun28.WeakRank.missing_four
