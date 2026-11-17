import FiniteQuartic
import QuarticHensel

namespace Sun28.LocalQuartics
noncomputable section

/-- At a prime of good reduction every unit twist has a primitive point.
A zero ordinate in the finite field lifts in the abscissa. All other
points lift in the ordinate. -/
theorem good_prime_cover {p b k : ℕ} [hp : Fact p.Prime] (odd : p≠2)
    (bunit : (b:ZMod p)≠0) (three : (3:ZMod p)≠0) (kunit : (k:ZMod p)≠0) :
    LocalCover p b k := by
  have map3 : PadicInt.toZMod (3:ℤ_[p])=(3:ZMod p) := map_ofNat _ _
  have two : (2:ZMod p)≠0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      (fun d=>odd ((Nat.dvd_prime Nat.prime_two).mp d |>.resolve_left hp.out.ne_one))
  have det : (1:ZMod p)*(3*b)-(-b)*1≠0 := by
    convert mul_ne_zero (mul_ne_zero two two) bunit using 1; ring
  obtain ⟨u,y,E⟩:=residue_point  odd (1:ZMod p) (-b) 1 (3*b) k det kunit
  simp only [one_mul] at E
  by_cases yz : y=0
  · rw [yz,zero_pow (by decide)] at E
    rcases mul_eq_zero.mp E.symm with first|last
    · have root := (mul_eq_zero.mp first).resolve_left kunit
      have eq : (b:ZMod p)=u^2 := by linear_combination -root
      have un : u≠0 := by intro e;apply bunit;simp [eq,e]
      obtain ⟨x,h⟩:=square_residue_lift (A:=(b:ℤ_[p])) odd un (by simpa [map3] using eq)
      exact at_root ⟨x,Or.inl h⟩
    · have eq : -3*(b:ZMod p)=u^2 := by linear_combination -last
      have un : u≠0 := by
        intro e
        exact (mul_ne_zero (neg_ne_zero.mpr three) bunit) (by simpa [e] using eq)
      obtain ⟨x,h⟩ := square_residue_lift (A:= -3*(b:ℤ_[p])) odd un (by simpa [map3] using eq)
      exact at_root ⟨x,Or.inr h⟩
  · let U : ℤ_[p] := (u.val:ℕ)
    have eq : PadicInt.toZMod ((k:ℤ_[p])*quarticForm (b:ℤ_[p]) U 1)=y^2 := by
      simpa [quarticForm,U,sub_eq_add_neg,mul_assoc,map3] using E.symm
    obtain ⟨Y,h⟩ := square_residue_lift odd yz eq
    exact ⟨U,1,Y,Or.inr isUnit_one,h⟩

end
end Sun28.LocalQuartics
#print axioms Sun28.LocalQuartics.good_prime_cover
