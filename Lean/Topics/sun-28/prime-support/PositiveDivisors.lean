import QuarticDivisors

namespace Sun28.PointLifts
noncomputable section

/-- In the nonzero square branch both integral quadratic values are positive. -/
theorem positive_left {b a d U V y : ℤ} (bp : 0<b) (ap : 0<a) (dp : 0<d)
    (fn : leftForm b a d U V≠0) (gn : b*rightForm b a d U V≠0)
    (E : y^2=b*leftForm b a d U V*rightForm b a d U V) : 0<leftForm b a d U V := by
  by_contra! nonpos
  have neg := lt_of_le_of_ne nonpos fn
  by_cases le : d≤a
  · have w := sub_nonneg.mpr le
    have h := add_nonneg (mul_nonneg w (sq_nonneg U))
      (mul_nonneg (mul_nonneg (by omega : 0≤3*a+d) bp.le) (sq_nonneg V))
    exact (not_lt_of_ge h) neg
  · have rne : rightForm b a d U V≠0 := right_ne_zero_of_mul gn
    have rn : rightForm b a d U V < 0 := by
      by_contra! r
      have pos := lt_of_le_of_ne r (Ne.symm rne)
      have h := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg bp neg) pos
      rw [← E] at h
      exact (sq_nonneg y).not_gt h
    have id : (a+3*d)*leftForm b a d U V+(d-a)*rightForm b a d U V=16*b*a*d*V^2 := by
      unfold leftForm rightForm;ring
    have negative := add_neg (mul_neg_of_pos_of_neg (by omega : 0<a+3*d) neg)
      (mul_neg_of_pos_of_neg (by omega : 0<d-a) rn)
    have nonnegative : 0≤16*b*a*d*V^2 := by positivity
    exact nonnegative.not_gt (id ▸ negative)

/-- Squareness removes repeated primes from the divisor bound. -/
theorem reduced_divisor {b θ n m D : ℤ} (sf : Squarefree D)
    (dv : D ∣ b*determinant b (n^2) (θ*m^2)) : D ∣ 2*b*θ*n*m := by
  apply (sf.dvd_pow_iff_dvd (by decide : 4 ≠ 0)).mp
  apply dvd_trans dv
  refine ⟨-b^2*θ^3*n^2*m^2,?_⟩
  unfold determinant;ring

def PositiveFibre (b θ n m : ℤ) : Prop :=
  ∃ U V : ℤ, U.natAbs.Coprime V.natAbs ∧ U^2-b*V^2≠0 ∧
    let F := leftForm b (n^2) (θ*m^2) U V
    let G := b*rightForm b (n^2) (θ*m^2) U V
    F=0 ∨ G=0 ∨ ∃ D u v : ℤ, 0<D ∧ Squarefree D ∧ D ∣ 2*b*θ*n*m ∧ F=D*u^2 ∧ G=D*v^2

theorem integral_iff_positive {b θ n m : ℤ} (bp : 0<b) (tp : 0<θ) (nn : n≠0) (mn : m≠0) :
    IntegralFibre b θ n m ↔ PositiveFibre b θ n m := by
  constructor
  · rintro ⟨U,V,Y,prim,L,E⟩
    refine ⟨U,V,prim,L,?_⟩
    dsimp only
    by_cases f : leftForm b (n^2) (θ*m^2) U V=0
    · exact Or.inl f
    by_cases g : b*rightForm b (n^2) (θ*m^2) U V=0
    · exact Or.inr (Or.inl g)
    obtain ⟨D,u,v,sf,hD,fu,gv⟩:=finite_descent prim f g E
    have pos := positive_left bp (sq_pos_of_ne_zero nn) (mul_pos tp (sq_pos_of_ne_zero mn)) f g E
    rw [fu] at pos
    have Dpos := pos_of_mul_pos_left pos (sq_nonneg u)
    exact Or.inr (Or.inr ⟨D,u,v,Dpos,sf,reduced_divisor sf hD,fu,gv⟩)
  · rintro ⟨U,V,prim,L,branches⟩
    rcases branches with f|g|⟨D,u,v,_,_,_,f,g⟩
    · exact ⟨U,V,0,prim,L,by simp [f]⟩
    · exact ⟨U,V,0,prim,L,by rw [mul_right_comm b _ _,g];ring⟩
    · exact ⟨U,V,D*u*v,prim,L,by rw [mul_right_comm b _ _,g,f];ring⟩

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.positive_left
#print axioms Sun28.PointLifts.reduced_divisor
#print axioms Sun28.PointLifts.integral_iff_positive
