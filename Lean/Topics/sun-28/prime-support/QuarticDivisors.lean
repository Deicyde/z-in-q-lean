import IntegralQuartic

namespace Sun28.PointLifts
open ZInQ.RouteK
noncomputable section

/-- The determinant of the two linear forms in (U²,V²). -/
def determinant (b a d : ℤ) := -16*b*a*d

/-- A common divisor of the two values divides the determinant on a
primitive direction. This includes any common prime powers. -/
theorem common_dvd_determinant {b a d U V e : ℤ}
    (prim : U.natAbs.Coprime V.natAbs)
    (L : e ∣ leftForm b a d U V) (R : e ∣ rightForm b a d U V) :
    e ∣ determinant b a d := by
  have hU : e ∣ determinant b a d*U^2 := by
    have h := dvd_sub (dvd_mul_of_dvd_right L (3*(a-d)*b))
      (dvd_mul_of_dvd_right R ((3*a+d)*b))
    convert h using 1
    unfold leftForm rightForm determinant
    ring
  have hV : e ∣ determinant b a d*V^2 := by
    have h := dvd_sub (dvd_mul_of_dvd_right R (a-d)) (dvd_mul_of_dvd_right L (a+3*d))
    convert h using 1
    unfold leftForm rightForm determinant
    ring
  have cp : IsCoprime U V := Int.isCoprime_iff_gcd_eq_one.mpr prim
  obtain ⟨i,j,bez⟩ := cp.pow (m:=2) (n:=2)
  obtain ⟨u,hu⟩ := hU
  obtain ⟨v,hv⟩ := hV
  refine ⟨i*u+j*v,?_⟩
  linear_combination i*hu+j*hv-(determinant b a d)*bez

private theorem common_kernel {f g y : ℤ} (fn : f≠0) (gn : g≠0) (E : y^2=f*g) :
    ∃ D u v : ℤ, Squarefree D ∧ f=D*u^2 ∧ g=D*v^2 := by
  obtain ⟨sf,u,un,hu⟩ := sqfInt_spec fn
  obtain ⟨sg,v,vn,hv⟩ := sqfInt_spec gn
  have union : f*y^2=g*f^2 := by linear_combination f*E
  have yn : y≠0 := fun h => (mul_ne_zero fn gn) (by simpa [h] using E.symm)
  have same : sqfInt f = sqfInt g := by
    rw [←sqfInt_mul_sq fn yn,union,sqfInt_mul_sq gn fn]
  exact ⟨sqfInt f,u,v,sf,hu,same.symm ▸ hv⟩

/-- Only signed squarefree divisors of 16 b² a d can occur in the
descent. D occurs in the equations F = D u² and bG = D v². -/
theorem finite_descent {b a d U V y : ℤ} (prim : U.natAbs.Coprime V.natAbs)
    (fn : leftForm b a d U V≠0) (gn : b*rightForm b a d U V≠0)
    (E : y^2=b*leftForm b a d U V*rightForm b a d U V) :
    ∃ D u v : ℤ, Squarefree D ∧ D ∣ b*determinant b a d ∧
      leftForm b a d U V=D*u^2 ∧ b*rightForm b a d U V=D*v^2 := by
  obtain ⟨D,u,v,sf,hf,hg⟩ := common_kernel (y:=y) fn gn (by linear_combination E)
  have df : D ∣ leftForm b a d U V := ⟨_,hf⟩
  have dg : D ∣ b*rightForm b a d U V := ⟨_,hg⟩
  have hU : D ∣ b*determinant b a d*U^2 := by
    have h := dvd_sub (dvd_mul_of_dvd_right df (b*(3*(a-d)*b)))
      (dvd_mul_of_dvd_right dg ((3*a+d)*b))
    convert h using 1
    unfold leftForm rightForm determinant
    ring
  have hV : D ∣ b*determinant b a d*V^2 := by
    have h := dvd_sub (dvd_mul_of_dvd_right dg (a-d)) (dvd_mul_of_dvd_right df (b*(a+3*d)))
    convert h using 1
    unfold leftForm rightForm determinant
    ring
  obtain ⟨i,j,bez⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr prim).pow (m:=2) (n:=2)
  obtain ⟨z,hz⟩ := hU
  obtain ⟨w,hw⟩ := hV
  refine ⟨D,u,v,sf,⟨i*z+j*w,?_⟩,hf,hg⟩
  linear_combination i*hz+j*hw-(b*determinant b a d)*bez

/-- The two zero branches preserve all horizontal sections. In the remaining
branch the divisibility condition is a finite restriction as soon as b a d≠0. -/
def DivisorFibre (b θ n m : ℤ) : Prop :=
  ∃ U V : ℤ, U.natAbs.Coprime V.natAbs ∧ U^2-b*V^2≠0 ∧
    let a := n^2
    let d := θ*m^2
    let F := leftForm b a d U V
    let G := b*rightForm b a d U V
    F=0 ∨ G=0 ∨ ∃ D u v : ℤ, Squarefree D ∧ D ∣ b*determinant b a d ∧ F=D*u^2 ∧ G=D*v^2

theorem integral_iff_divisors (b θ n m : ℤ) : IntegralFibre b θ n m ↔ DivisorFibre b θ n m := by
  constructor
  · rintro ⟨U,V,Y,prim,L,E⟩
    refine ⟨U,V,prim,L,?_⟩
    dsimp only
    by_cases f : leftForm b (n^2) (θ*m^2) U V=0
    · exact Or.inl f
    by_cases g : b*rightForm b (n^2) (θ*m^2) U V=0
    · exact Or.inr (Or.inl g)
    exact Or.inr (Or.inr (finite_descent prim f g E))
  · rintro ⟨U,V,prim,L,branches⟩
    rcases branches with f|g|⟨D,u,v,_,_,f,g⟩
    · exact ⟨U,V,0,prim,L,by simp [f]⟩
    · exact ⟨U,V,0,prim,L,by rw [mul_right_comm b _ _,g];ring⟩
    · refine ⟨U,V,D*u*v,prim,L,?_⟩
      rw [mul_right_comm b _ _,g,f];ring

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.common_dvd_determinant
#print axioms Sun28.PointLifts.finite_descent
#print axioms Sun28.PointLifts.integral_iff_divisors
