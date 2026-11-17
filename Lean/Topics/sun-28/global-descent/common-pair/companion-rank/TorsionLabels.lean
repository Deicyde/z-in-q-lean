import MarkedFifthClass

namespace Sun28.CompanionRank
open Sun28.SelmerRealization Sun28.MarkedDescent ZInQ.RouteK
noncomputable section

private theorem signed_one : sqf (1:ℚ) = 1 :=
  sqf_eq_of_eq_mul_sq (d:=1) (t:=(1:ℚ)) squarefree_one one_ne_zero (by norm_num)

private theorem negative_label {x : ℚ} (hx : x < 0) : sqf x < 0 := by
  obtain ⟨_,w,_,eq⟩ := sqf_spec hx.ne
  by_contra! h
  have pos : 0 ≤ (sqf x : ℚ) := by exact_mod_cast h
  exact hx.not_ge (eq ▸ mul_nonneg pos (sq_nonneg w))

theorem label_zero (l : ℕ) : labels l 0 = (1,1) :=
  Prod.ext signed_one signed_one

/-- The abscissae 0 and −3l have negative second label; the abscissa l
has label (l,1). The identity is the remaining two-torsion point. -/
theorem two_label {l : ℕ} (lp : 0<l) (sf : Squarefree l) {P : RationalPoint l}
    (two : (2:ℕ) • P=0) :
    P=0 ∨ (labels l P).2<0 ∨ labels l P=((l:ℤ),1) := by
  have pos : 0<(l:ℚ) := by exact_mod_cast lp
  have neg := negative_label (neg_lt_zero.mpr pos)
  have number : sqf (l:ℚ)=(l:ℤ) :=
    sqf_eq_of_eq_mul_sq (t:=(1:ℚ)) (Int.squarefree_natCast.mpr sf) one_ne_zero (by simp)
  cases P with
  | zero => exact Or.inl rfl
  | @some x y ns =>
    rw [ZInQ.two_nsmul_some_eq_zero_iff,neg_y] at two
    obtain rfl : y=0 := by linarith
    have eq := equation.mp ns.1
    change (0:ℚ)^2=x*(x-l)*(x+3*l) at eq
    have H : x*(x-l)*(x+3*l)=0 := by nlinarith only [eq]
    rcases mul_eq_zero.mp H with h|h
    · rcases mul_eq_zero.mp h with h|h
      · subst x
        exact Or.inr (Or.inl (by simpa only [labels,raw,↓reduceIte] using neg))
      · obtain rfl := sub_eq_zero.mp h
        exact Or.inr (Or.inr (by simp only [labels,raw,ite_eq_right pos.ne',↓reduceIte,number,signed_one]))
    · have h' : x= -3*(l:ℚ) := by linarith
      subst x
      have nz : -3*(l:ℚ)≠0 := by linarith
      have nn : -3*(l:ℚ)≠l := by linarith
      exact Or.inr (Or.inl (by simpa only [labels,raw,ite_eq_right nz,ite_eq_right nn,↓reduceIte] using neg))

/-- On these twists the image of doubling meets rational two-torsion
only in the identity. -/
theorem two_double {l : ℕ} (big : 1<l) (sf : Squarefree l) {P Q : RationalPoint l}
    (two : (2:ℕ) • P=0) (double : (2:ℕ) • Q=P) : P=0 := by
  have lp : 0<l := by omega
  have same : labels l P = (1,1) := by
    rw [←label_zero l]
    apply Sun28.Corank.quotient_label lp
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    exact ⟨Q,by simpa only [sub_zero] using double⟩
  rcases two_label lp sf two with zero|neg|first
  · exact zero
  · rw [same] at neg; norm_num at neg
  · have e : (1:ℤ)=l := congrArg Prod.fst (same.symm.trans first)
    omega

/-- Every finite-order rational point has the same class modulo doubling
as a rational two-torsion point. No finite-generation hypothesis is needed. -/
theorem torsion_representative {l : ℕ} (big : 1<l) (sf : Squarefree l)
    {P : RationalPoint l} (finite : IsOfFinAddOrder P) :
    ∃ T : RationalPoint l, (2:ℕ) • T=0 ∧
      (QuotientAddGroup.mk P : ModTwo l)=QuotientAddGroup.mk T := by
  have down (j : ℕ) : ∀ V : RationalPoint l, (2^j : ℕ) • V=0 → (2:ℕ) • V=0 := by
    induction j with
    | zero =>
      intro V h
      simp only [pow_zero,one_smul] at h
      simp [h]
    | succ j ih =>
      intro V h
      apply two_double big sf (Q:=V) _ rfl
      apply ih
      rw [←mul_smul,←pow_succ]
      exact h
  obtain ⟨a,m,odd,ord⟩ := Nat.exists_eq_two_pow_mul_odd finite.addOrderOf_pos.ne'
  have h : (2^a : ℕ) • (m • P)=0 := by
    rw [←mul_smul,←ord,addOrderOf_nsmul_eq_zero]
  refine ⟨m • P,down a _ h,?_⟩
  symm
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  obtain ⟨v,hv⟩ := odd
  have hm : m=2*v+1 := by omega
  refine ⟨v • P,?_⟩
  change (2:ℕ) • (v • P)=m • P-P
  rw [hm,add_smul,one_smul,←mul_smul]
  abel

theorem marked_label_infinite {b l : ℕ} (bb : 1<b) (bl : b<l) (sf : Squarefree l)
    {P : RationalPoint l} (mark : labels l P=((b:ℤ),1)) : ¬IsOfFinAddOrder P := by
  intro finite
  obtain ⟨T,two,same⟩ := torsion_representative (by omega) sf finite
  have lab := (Sun28.Corank.quotient_label (by omega) same).symm.trans mark
  rcases two_label (by omega) sf two with rfl|neg|number
  · have e : (1:ℤ)=b := congrArg Prod.fst ((label_zero l).symm.trans lab)
    omega
  · rw [lab] at neg;norm_num at neg
  · have e : (l:ℤ)=b := congrArg Prod.fst (number.symm.trans lab)
    omega

end
end Sun28.CompanionRank

#print axioms Sun28.CompanionRank.two_label
#print axioms Sun28.CompanionRank.two_double
#print axioms Sun28.CompanionRank.torsion_representative
#print axioms Sun28.CompanionRank.marked_label_infinite
