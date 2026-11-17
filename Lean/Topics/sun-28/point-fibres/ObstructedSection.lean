import PreparedExample
import CoverTests

namespace Sun28.PointFibres
open Sun28.PointDescent Sun28.PrescribedPoints Sun28.PairedClasses Sun28.PreparedPoles
  Sun28.TwistExtension Sun28.TwistRank Sun28.FixedPreparation
noncomputable section

/-- A prepared example from the earlier, three-prime preparation. -/
theorem section_409 : AuxiliaryCover 17 409 ∧ NonzeroPair 17 409 := by
  have cov : AuxiliaryCover 17 409:=⟨-17/9,-544/81,by norm_num,by norm_num,by norm_num⟩
  exact ⟨cov,nonzero_of_auxiliary (by norm_num) (by norm_num) cov⟩

/-- Both target ordinates are nonzero on this old control, although the single section fails. -/
theorem section_577 : ¬AuxiliaryCover 17 577 ∧ NonzeroPair 17 577 := by
  refine ⟨mod_five_obstruction (b:=17) (θ:=577) (by decide)
    (show Nat.Prime 577 by norm_num).squarefree (Or.inl (by decide)) (Or.inl (by decide)),?_⟩
  exact ⟨161823,501/2,6513/2,9792804015/8,21486500098245/8,by norm_num,by norm_num,
    by norm_num,by norm_num,by norm_num,by norm_num,by norm_num⟩

private theorem no_lift {p d : ℕ} (test : ∀ r : ZMod p, r^2≠(d:ZMod p)) :
    ¬LocalSquareAt p d := by
  intro lifts
  obtain ⟨r,hr⟩:=lifts 1
  rw [pow_one] at hr
  have h:=(ZMod.intCast_eq_intCast_iff (r^2) (d:ℤ) p).mpr hr
  exact test (r:ZMod p) (by simpa using h)

theorem old_controls_outside : ¬FixedSquares 577 ∧ ¬FixedSquares 409 := by
  constructor
  · intro h
    exact no_lift (p:=5) (d:=577) (by decide) (h 5 (by decide) (by decide) (by decide)).2
  · intro h
    exact no_lift (p:=7) (d:=409) (by decide) (h 7 (by decide) (by decide) (by decide)).2

/-- For a prime second class the existing factorized route is subsumed by the single signed quartic. -/
theorem prime_factor_pair_is_one {b θ : ℕ} (bp : 0<b) (pr : θ.Prime)
    (f : FactorPair b θ) : OneQuartic (b:ℚ) (θ:ℚ) := by
  obtain ⟨d,e,_,_,de,F,G⟩:=f
  rcases (Nat.dvd_prime pr).mp (show d∣θ from ⟨e,de⟩) with d1|dt
  · subst d
    rw [one_mul] at de
    exact one_of_factor bp pr.pos (de ▸ G)
  · exact one_of_factor bp pr.pos (dt ▸ F)

/-- Both signed homogeneous curves retain the points at infinity. -/
def SignedQuartic (b d : ℚ) : Prop :=
  ∃ x z y : ℚ, (x≠0 ∨ z≠0) ∧ y≠0 ∧ y^2=d*quartic b x z

theorem squareclass_iff_signed {b d : ℚ} (dn : d≠0) :
    (∃ x z h : ℚ, d=quartic b x z*h^2) ↔ SignedQuartic b d := by
  constructor
  · rintro ⟨x,z,h,E⟩
    have hn : h≠0:=by rintro rfl;apply dn;simpa using E
    have lin : x≠0 ∨ z≠0:=by
      by_contra! both
      obtain ⟨rfl,rfl⟩:=both
      apply dn;simpa [quartic] using E
    exact ⟨x,z,d/h,lin,div_ne_zero dn hn,by field_simp;linear_combination E⟩
  · rintro ⟨x,z,y,_,yn,E⟩
    exact ⟨x,z,d/y,by field_simp;linear_combination E⟩

theorem one_iff_signed {b θ : ℚ} (tn : θ≠0) :
    OneQuartic b θ ↔ SignedQuartic b θ ∨ SignedQuartic b (-3*θ) := by
  have mt : -3*θ≠0:=mul_ne_zero (by norm_num) tn
  constructor
  · rintro ⟨x,z,y,A|B⟩
    · exact Or.inl ((squareclass_iff_signed tn).mp ⟨x,z,y,A⟩)
    · exact Or.inr ((squareclass_iff_signed mt).mp ⟨x,z,y,B⟩)
  · rintro (A|B)
    · obtain ⟨x,z,y,E⟩:=(squareclass_iff_signed tn).mpr A
      exact ⟨x,z,y,Or.inl E⟩
    · obtain ⟨x,z,y,E⟩:=(squareclass_iff_signed mt).mpr B
      exact ⟨x,z,y,Or.inr E⟩

end
end Sun28.PointFibres
#print axioms Sun28.PointFibres.section_409
#print axioms Sun28.PointFibres.section_577
#print axioms Sun28.PointFibres.old_controls_outside
#print axioms Sun28.PointFibres.prime_factor_pair_is_one
#print axioms Sun28.PointFibres.squareclass_iff_signed
#print axioms Sun28.PointFibres.one_iff_signed
