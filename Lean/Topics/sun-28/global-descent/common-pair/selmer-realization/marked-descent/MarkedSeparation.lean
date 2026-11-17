import ExplicitHalving
import ActualPointRank

namespace Sun28.MarkedDescent
open Sun28.SelmerRealization ZInQ.Descent ZInQ.RouteK WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
variable {l : ℕ}

private theorem sqc_rep (q : ℚ) : sqc ((sqf q:ℤ):ℚ)=sqc q := by
  by_cases nq : q=0
  · subst q;norm_num [sqf,sqfInt]
  obtain ⟨_,u,un,eq⟩:=sqf_spec nq
  conv_rhs => rw [eq,sqc_mul_sq _ un]

/-- Evaluation at the roots −3l,l recovers the ordered marked labels,
including the infinity and all three exceptional affine abscissas. -/
theorem character_labels (lp : 0<l) (P : RationalPoint l) :
    (rootClass l (-3*l) P, rootClass l l P)=
    (sqc ((labels l P).1:ℚ),sqc ((labels l P).2:ℚ)) := by
  have ln : (l:ℚ)≠0 := by exact_mod_cast lp.ne'
  have p : (0:ℚ)<l := by exact_mod_cast lp
  cases P with
  | zero => simp [rootClass,labels,raw,sqc_rep]
  | @some x y h =>
    simp only [at_affine,labels,sqc_rep,raw]
    by_cases x0 : x=0
    · subst x
      have h3 : (0:ℚ)≠ -3*l := by linarith
      simp only [ite_eq_right h3,ite_eq_right ln.symm,ite_true,zero_sub];congr 2;ring
    by_cases x1 : x=l
    · subst x
      have h3 : (l:ℚ)≠ -3*l := by linarith
      have d : derivativeAt l l=(2*(l:ℚ))^2 := by unfold derivativeAt;ring
      simp only [x0,h3,ite_false,ite_true,d,sqc_sq,sqc_one,Prod.mk.injEq,and_true]
      rw [show (l:ℚ)- -3*l=l*(2:ℚ)^2 by ring,sqc_mul_sq _ (by norm_num)]
    by_cases xm : x= -3*l
    · subst x
      have d : derivativeAt l (-3*l)=3*(2*(l:ℚ))^2 := by unfold derivativeAt;ring
      simp only [x0,x1,ite_false,ite_true,d]
      rw [sqc_mul_sq _ (mul_ne_zero (by norm_num) ln),
        show (-3*(l:ℚ))-l=(-l)*(2:ℚ)^2 by ring,sqc_mul_sq _ (by norm_num)]
    simp only [x0,x1,xm,ite_false]
    congr 2
    ring

private theorem difference_square (P : RationalPoint l) (e : ℚ) {x y : ℚ}
    (ns : (twistCurve l).toAffine.Nonsingular x y) (hP : P=.some x y ns)
    (h : rootClass l e P=1) : ∃ r : ℚ, x-e=r^2 := by
  rw [hP,at_affine] at h
  by_cases xe : x=e
  · exact ⟨0,by rw [xe];ring⟩
  rw [ite_eq_right xe] at h
  obtain ⟨r,_,R⟩:=(sqc_eq_one_iff_exists (sub_ne_zero.mpr xe)).mp h
  exact ⟨r,R⟩

theorem half_of_characters (lp : 0<l) (P : RationalPoint l)
    (h₁ : rootClass l (-3*l) P=1) (h₂ : rootClass l l P=1) :
    ∃ Q : RationalPoint l, 2 • Q=P := by
  have pos : (0:ℚ)<l := by exact_mod_cast lp
  cases P with
  | zero => exact ⟨0,by change (2:ℕ) • (0:RationalPoint l)=0;simp⟩
  | @some x y ns =>
    obtain ⟨b,B⟩:=difference_square _ _ ns rfl h₂
    obtain ⟨c,C⟩:=difference_square _ _ ns rfl h₁
    have C' : x+3*l=c^2 := by linear_combination C
    have A : ∃ a : ℚ, x=a^2 := by
      by_cases b0 : b=0
      · exact ⟨c/2,by rw [b0] at B;linear_combination (3*B+C')/4⟩
      have c0 : c≠0 := by intro H;rw [H] at C';nlinarith [sq_nonneg b]
      use y/(b*c)
      have eq:=equation.mp ns.1
      rw [B,C'] at eq
      field_simp [b0,c0]
      linear_combination -eq
    obtain ⟨a,A⟩:=A
    exact half_of_squares lp ns A B C'

/-- Full separation on precisely the Weierstrass model used by the marked cover. -/
theorem kummer_separation (lp : 0<l) : KummerSeparation l := by
  intro P Q E
  have pos : (0:ℚ)<l := by exact_mod_cast lp
  have eq:= (character_labels lp P).trans ((congrArg (fun ab : ℤ × ℤ =>
      (sqc (ab.1:ℚ),sqc (ab.2:ℚ))) E).trans (character_labels lp Q).symm)
  have H (e : ℚ) (he : e*(e-l)*(e+3*l)=0) (hn : derivativeAt l e≠0)
      (equal : rootClass l e P=rootClass l e Q) : rootClass l e (P-Q)=1 := by
    rw [sub_eq_add_neg,class_add he hn,class_neg,equal,SqClass.mul_self]
  have one := H (-3*l) (by ring) (by unfold derivativeAt;nlinarith [sq_pos_of_pos pos])
    (congrArg Prod.fst eq)
  have two := H l (by ring) (by unfold derivativeAt;nlinarith [sq_pos_of_pos pos])
    (congrArg Prod.snd eq)
  exact QuotientAddGroup.eq_iff_sub_mem.mpr (half_of_characters lp _ one two)

theorem prepared_scalar [AddGroup.FG (RationalPoint n)]
    (finite : FiniteDescent n 526361 1) (point : ∃ P : RationalPoint n, ¬IsOfFinAddOrder P) :
    ∃ e z : ℚ, Sun28.Ordinary.poleBranch 15 Sun28.PointFibres.pole e z :=
  prepared_scalar_of_infinite_point (kummer_separation (by decide)) finite point

end
end Sun28.MarkedDescent
#print axioms Sun28.MarkedDescent.character_labels
#print axioms Sun28.MarkedDescent.half_of_characters
#print axioms Sun28.MarkedDescent.kummer_separation
#print axioms Sun28.MarkedDescent.prepared_scalar
