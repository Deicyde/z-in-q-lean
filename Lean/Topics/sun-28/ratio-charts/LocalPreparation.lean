import AuxiliaryLocal
import GoodQuartic

namespace Sun28.LocalQuartics
open Sun28.PairedClasses Sun28.PreparedPoles
noncomputable section

private theorem lift_square_nat {p a : ℕ} [Fact p.Prime] (odd : p≠2)
    (nz : (a:ZMod p)≠0) (sq : IsSquare (a:ZMod p)) : ∃ y : ℤ_[p], y^2=a := by
  obtain ⟨x,hx⟩:=sq
  have xn : x≠0 := by intro e;apply nz;rw [hx,e,mul_zero]
  exact square_residue_lift odd xn (by simpa [pow_two] using hx)

private theorem root_cover {p b k : ℕ} [Fact p.Prime] (H : ∃ x:ℤ_[p], x^2=b) :
    LocalCover p b k := by
  obtain ⟨x,h⟩:=H
  exact at_root ⟨x,Or.inl h⟩

theorem local_preparation {b θ q : ℕ} (adm : AdmissiblePair b θ)
    (pr : q.Prime) (big : max b θ<q) (prog : q≡1 [MOD 24*b*θ])
    (p : ℕ) [hp : Fact p.Prime] : LocalCover p b q ∧ LocalCover p b (q*θ) := by
  obtain ⟨bp,tp,sb,st,cop,b6,t6,b24,t24,bt,tb⟩:=adm
  have q24 : q≡1 [MOD 24] := prog.of_dvd ⟨b*θ,by ring⟩
  have t24' : θ≡1 [MOD 24] := t24
  by_cases p2 : p=2
  · subst p
    have q8 := q24.of_dvd (by decide : 8∣24)
    have t8 := t24'.of_dvd (by decide : 8∣24)
    exact ⟨at_infinity (dyadic_one_mod_eight _ q8),at_infinity (dyadic_one_mod_eight _ (by simpa using q8.mul t8))⟩
  by_cases p3 : p=3
  · subst p
    have q3 : (q:ZMod 3)=1 := by simpa using (ZMod.natCast_eq_natCast_iff q 1 3).mpr (q24.of_dvd (by decide))
    have t3 : (θ:ZMod 3)=1 := by simpa using (ZMod.natCast_eq_natCast_iff θ 1 3).mpr (t24'.of_dvd (by decide))
    have c (n : ℕ) (h : (n:ZMod 3)=1) : LocalCover 3 b n := at_infinity
      (lift_square_nat (by decide) (h ▸ one_ne_zero) (h ▸ IsSquare.one))
    exact ⟨c q q3,c _ (by simp [q3,t3])⟩
  by_cases pb : p∣b
  · have div : p∣24*b*θ := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right pb 24) θ
    have q1 : (q:ZMod p)=1 := by simpa using (ZMod.natCast_eq_natCast_iff q 1 p).mpr (prog.of_dvd div)
    have t0 : (θ:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr
      (fun pt=>hp.out.not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd pb pt))
    have tS := residue_of_tower (tb p hp.out pb)
    have qS : IsSquare (q:ZMod p) := q1 ▸ IsSquare.one
    exact ⟨at_infinity (lift_square_nat p2 (q1 ▸ one_ne_zero) qS),at_infinity
      (lift_square_nat p2 (by simpa [q1] using t0)
        (by simpa using qS.mul tS))⟩
  have b0 : (b:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr pb
  by_cases pt : p∣θ
  · have w := lift_square_nat p2 b0 (residue_of_tower (bt p hp.out pt))
    exact ⟨root_cover w,root_cover w⟩
  by_cases pq : p=q
  · subst p
    have b1 : 1<b := by omega
    have w := lift_square_nat p2 b0 (square_at_auxiliary b1 b24 pr (lt_of_le_of_lt (le_max_left ..) big) prog)
    exact ⟨root_cover w,root_cover w⟩
  have q0 : (q:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr
    (fun d=>pq ((Nat.prime_dvd_prime_iff_eq hp.out pr).mp d))
  have t0 : (θ:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr pt
  have three : (3:ZMod p)≠0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 3 p).not.mpr
      (fun d=>p3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp d))
  exact ⟨good_prime_cover p2 b0 three q0,good_prime_cover p2 b0 three (by simpa using mul_ne_zero q0 t0)⟩

theorem real_cover {b k : ℕ} (kp : 0<k) :
    ∃ U V Y : ℝ, (U≠0 ∨ V≠0) ∧ Y^2=k*quarticForm (b:ℝ) U V := by
  exact ⟨1,0,Real.sqrt k,Or.inl one_ne_zero,by simp [quarticForm,Real.sq_sqrt (by positivity : 0≤(k:ℝ))]⟩

/-- One rational scalar for both quartics, simultaneously at every prime and at infinity. -/
theorem common_local_twists {b θ : ℕ} (a : AdmissiblePair b θ) (bound : ℕ) :
    ∃ q>max bound (max b θ), q.Prime ∧ q≡1 [MOD 24*b*θ] ∧
      (∀ p : ℕ, ∀ [Fact p.Prime], LocalCover p b q ∧ LocalCover p b (q*θ)) ∧
      (∀ k ∈ [q,q*θ], ∃ U V Y : ℝ, (U≠0 ∨ V≠0) ∧ Y^2=k*quarticForm (b:ℝ) U V) := by
  obtain ⟨q,big,pr,prog⟩:=fresh_progression a.1 a.2.1 bound
  refine ⟨q,big,pr,prog,fun p _=>local_preparation a pr (lt_of_le_of_lt (le_max_right ..) big) prog p,?_⟩
  intro k h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl
  · exact real_cover pr.pos
  · exact real_cover (Nat.mul_pos pr.pos a.2.1)

end
end Sun28.LocalQuartics
#print axioms Sun28.LocalQuartics.local_preparation
#print axioms Sun28.LocalQuartics.real_cover
#print axioms Sun28.LocalQuartics.common_local_twists
