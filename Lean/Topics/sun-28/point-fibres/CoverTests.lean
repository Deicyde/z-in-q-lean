import FactorDescent

namespace Sun28.PointFibres
open Sun28.PointDescent
noncomputable section

/-- Homogeneous numerator, denominator and ordinate of an affine rational point. -/
def PrimitiveModel (b θ : ℕ) : Prop :=
  ∃ x y z : ℤ, x≠0 ∧ y≠0 ∧ z≠0 ∧ x.natAbs.Coprime y.natAbs ∧
    (θ:ℤ)*z^2=smallFactor b x y*largeFactor b x y

theorem primitive_model_iff {b θ : ℕ} (bp : 0<b) (sf : Squarefree θ) :
    AuxiliaryCover (b:ℚ) (θ:ℚ) ↔ PrimitiveModel b θ := by
  constructor
  · intro H
    obtain ⟨x,y,d,f,g,a,c,xn,yn,cop,_,ds,_,eq,an,cn,S,L,P⟩:=partition_of_auxiliary bp sf H
    have nz : d*a*c≠0:=mul_ne_zero (mul_ne_zero ds.ne_zero an.ne') cn.ne'
    have mag : (smallFactor b x y*largeFactor b x y).natAbs=θ*(d*a*c)^2 := by
      rw [Int.natAbs_mul,S,L,eq];ring
    refine ⟨x,y,((d*a*c:ℕ):ℤ),xn,yn,by exact_mod_cast nz,cop,?_⟩
    rw [←Int.natAbs_of_nonneg P.le,mag]
    push_cast
    ring
  · rintro ⟨x,y,z,xn,yn,zn,_,E⟩
    have yy : (y:ℚ)≠0:=by exact_mod_cast yn
    refine ⟨(x:ℚ)/y,(z:ℚ)/y^2,div_ne_zero (by exact_mod_cast xn) yy,
      div_ne_zero (by exact_mod_cast zn) (pow_ne_zero _ yy),?_⟩
    unfold smallFactor largeFactor at E
    have H : (θ:ℚ)*z^2=(x^2-(b:ℚ)*y^2)*(x^2-81*(b:ℚ)*y^2) := by exact_mod_cast E
    field_simp
    linear_combination H

/-- At five the two factors coincide and a primitive pair avoids their common zero. -/
theorem mod_five_obstruction {b θ : ℕ} (bp : 0<b) (sf : Squarefree θ)
    (hb : (b:ZMod 5)=2 ∨ (b:ZMod 5)=3) (ht : (θ:ZMod 5)=2 ∨ (θ:ZMod 5)=3) :
    ¬AuxiliaryCover (b:ℚ) (θ:ℚ) := by
  intro cov
  obtain ⟨x,y,z,_,_,_,cop,e⟩:=(primitive_model_iff bp sf).mp cov
  have h := congrArg (Int.castRingHom (ZMod 5)) e
  have hh : (θ:ZMod 5)*(z:ZMod 5)^2=((x:ZMod 5)^2-(b:ZMod 5)*(y:ZMod 5)^2)^2 := by
    simpa [smallFactor,largeFactor,show (81:ZMod 5)=1 by decide,sq] using h
  have rhs : ∀ (T W A:ZMod 5), (T=2 ∨ T=3) → T*W^2=A^2 → A=0:=by decide
  have anis : ∀ (B X Y:ZMod 5), (B=2 ∨ B=3) → X^2-B*Y^2=0 → X=0 ∧ Y=0:=by decide
  obtain ⟨xx,yy⟩:=anis _ _ _ hb (rhs _ _ _ ht hh)
  have X : (5:ℤ)∣x := (ZMod.intCast_zmod_eq_zero_iff_dvd x 5).mp xx
  have Y : (5:ℤ)∣y := (ZMod.intCast_zmod_eq_zero_iff_dvd y 5).mp yy
  exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1<5)
    (by simpa using Int.natAbs_dvd_natAbs.mpr X) (by simpa using Int.natAbs_dvd_natAbs.mpr Y)) cop

/-- The two prescribed classes can be exchanged on this section. -/
def BranchCover (m b θ : ℚ) : Prop :=
  ∃ k w : ℚ, k≠0 ∧ w≠0 ∧ θ*w^2=(k^2-b)*(k^2-m*b)

theorem branch_swap {m b θ : ℚ} (mn : m≠1) (tn : θ≠0)
    (H : BranchCover m b θ) : BranchCover m θ b := by
  obtain ⟨k,w,kn,wn,E⟩:=H
  have V : k^2-m*b≠0:=right_ne_zero_of_mul (E ▸ mul_ne_zero tn (pow_ne_zero _ wn))
  have W : (m-1)*k*(k^2-m*b)≠0:=mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr mn) kn) V
  refine ⟨(k^2-m*b)/w,(m-1)*k*(k^2-m*b)/w^2,div_ne_zero V wn,
    div_ne_zero W (pow_ne_zero _ wn),?_⟩
  have T : θ=(k^2-b)*(k^2-m*b)/w^2:=(eq_div_iff (pow_ne_zero _ wn)).mpr E
  rw [T]
  ring

theorem branch_reciprocity {m b θ : ℚ} (mn : m≠1) (bn : b≠0) (tn : θ≠0) :
    BranchCover m b θ ↔ BranchCover m θ b :=
  ⟨branch_swap mn tn,branch_swap mn bn⟩

theorem auxiliary_reciprocity {b θ : ℚ} (bn : b≠0) (tn : θ≠0) :
    AuxiliaryCover b θ ↔ AuxiliaryCover θ b :=
  branch_reciprocity (m:=81) (by norm_num) bn tn

end
end Sun28.PointFibres
#print axioms Sun28.PointFibres.primitive_model_iff
#print axioms Sun28.PointFibres.mod_five_obstruction
#print axioms Sun28.PointFibres.branch_swap
#print axioms Sun28.PointFibres.branch_reciprocity
#print axioms Sun28.PointFibres.auxiliary_reciprocity
