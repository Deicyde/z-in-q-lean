import MarkedFifthClass

namespace Sun28.Corank
open Sun28.SelmerRealization Sun28.MarkedDescent ZInQ.RouteK
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section

/-- The fixed twist has no nonzero rational point of order two which is
divisible by two in the rational point group. -/
theorem two_torsion_double {P Q : RationalPoint n} (two : (2:ℕ) • P=0)
    (half : (2:ℕ) • Q=P) : P=0 := by
  have same : labels n P=labels n 0 := by
    apply quotient_label (by decide : 0<n)
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    exact ⟨Q,by simpa only [sub_zero] using half⟩
  have one : sqf (1:ℚ)=1 := sqf_eq_of_eq_mul_sq (d:=1) (t:=(1:ℚ)) squarefree_one one_ne_zero (by norm_num)
  have ln : (0:ℚ)<n := by norm_num [n]
  have neg : sqf (-(n:ℚ)) ≠ 1 := by
    obtain ⟨_,w,_,eq⟩ := sqf_spec (neg_ne_zero.mpr ln.ne')
    intro h
    rw [h,Int.cast_one,one_mul] at eq
    nlinarith [sq_nonneg w]
  have nat : sqf (n:ℚ)=(n:ℤ) := by
    apply sqf_eq_of_eq_mul_sq (t:=(1:ℚ)) (Int.squarefree_natCast.mpr n_shape.2.1) one_ne_zero
    simp
  change labels n P=(sqf 1,sqf 1) at same
  rw [one] at same
  cases P with
  | zero => rfl
  | @some x y ns =>
    rw [ZInQ.two_nsmul_some_eq_zero_iff,neg_y] at two
    obtain rfl : y=0 := by linarith
    have eq := equation.mp ns.1
    change (0:ℚ)^2=x*(x-n)*(x+3*n) at eq
    have roots : x=0 ∨ x=(n:ℚ) ∨ x= -3*(n:ℚ) := by
      have H : x*(x-n)*(x+3*n)=0 := by nlinarith only [eq]
      rcases mul_eq_zero.mp H with h|h
      · rcases mul_eq_zero.mp h with h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl (sub_eq_zero.mp h))
      · exact Or.inr (Or.inr (by linarith))
    exfalso
    rcases roots with rfl|rfl|rfl
    · exact neg (by simpa only [labels,raw,↓reduceIte] using congrArg Prod.snd same)
    · have e : sqf (n:ℚ)=1 := by
        simpa only [labels,raw,ite_eq_right ln.ne',↓reduceIte] using congrArg Prod.fst same
      rw [nat] at e
      norm_num [n] at e
    · have nz : -3*(n:ℚ)≠0 := by linarith
      have nn : -3*(n:ℚ)≠n := by linarith
      exact neg (by simpa only [labels,raw,ite_eq_right nz,ite_eq_right nn,↓reduceIte] using congrArg Prod.snd same)

/-- All rational points of two-power order are killed by two. -/
theorem torsion_two_power (j : ℕ) : torsionAt (RationalPoint n) (2^(j+1)) = torsionAt (RationalPoint n) 2 := by
  have down (i : ℕ) : ∀ P : RationalPoint n, (2^(i+1) : ℕ) • P=0 → (2:ℕ) • P=0 := by
    induction i with
    | zero => simp
    | succ i ih =>
      intro P h
      have h' : (2^(i+1) : ℕ) • ((2:ℕ) • P)=0 := by
        rw [←mul_smul,←pow_succ];exact h
      exact two_torsion_double (ih _ h') rfl
  ext P
  change (2^(j+1) : ℕ) • P=0 ↔ (2:ℕ) • P=0
  exact ⟨down j P,fun h=> by rw [pow_succ,mul_smul,h]; exact nsmul_zero _⟩

/-- The entire cardinality sequence on this curve, in either rank alternative. -/
theorem fixed_higher_card [AddGroup.FG (RationalPoint n)] (K : PrimaryData (RationalPoint n))
    (comparison : LocalComparison n K) (j : ℕ) : Nat.card (K.sel (j+1)) = 4*2^(j+1) := by
  rw [(fixed_dichotomy K comparison).2.2,torsion_two_power,
    four_torsion (by decide : 0<n)]

end
end Sun28.Corank

#print axioms Sun28.Corank.two_torsion_double
#print axioms Sun28.Corank.torsion_two_power
#print axioms Sun28.Corank.fixed_higher_card
