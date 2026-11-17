import LocalPreparation

namespace Sun28.LocalQuartics
open Sun28.PairedClasses
noncomputable section

/-- The same scalar has the squarefreeness and coprimality of the integer
twist in the original point problem. The auxiliary primes are unbounded. -/
theorem admissible_local_twists {b θ : ℕ} (a : AdmissiblePair b θ) (bound : ℕ) :
    ∃ q > max bound (max b θ), q.Prime ∧ q≡1 [MOD 24*b*θ] ∧ Squarefree (b*q) ∧
      (b*q).Coprime (6*θ) ∧ (∀ p : ℕ, ∀ [Fact p.Prime], LocalCover p b q ∧ LocalCover p b (q*θ)) ∧
      (∀ k ∈ [q,q*θ], ∃ U V Y : ℝ, (U≠0 ∨ V≠0) ∧ Y^2=k*quarticForm (b:ℝ) U V) := by
  obtain ⟨q,big,pr,prog,localPoints,realPoints⟩:=common_local_twists a bound
  obtain ⟨bp,tp,sb,_,cop,b6,_,bm,_⟩:=a
  have bq : b<q := (le_max_left b θ).trans_lt ((le_max_right bound _).trans_lt big)
  have tq : θ<q := (le_max_right b θ).trans_lt ((le_max_right bound _).trans_lt big)
  have q6 : 6<q := by omega
  have cb : q.Coprime b := pr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt bp bq)
  have ct : q.Coprime θ := pr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt tp tq)
  have c6 : q.Coprime 6 := pr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) q6)
  exact ⟨q,big,pr,prog,(Nat.squarefree_mul cb.symm).mpr ⟨sb,pr.squarefree⟩,
    (b6.mul_right cop).mul_left (c6.mul_right ct),localPoints,realPoints⟩

end
end Sun28.LocalQuartics
#print axioms Sun28.LocalQuartics.admissible_local_twists
