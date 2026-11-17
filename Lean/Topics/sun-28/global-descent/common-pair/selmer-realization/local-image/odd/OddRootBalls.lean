import OddCoverChart
import ZInQKernel.RouteK.Selmer.PadicSquare

namespace Sun28.MarkedOdd
open Sun28.SelmerRealization ZInQ.RouteK.Selmer
variable {p : ℕ} [Fact p.Prime]
abbrev Qp (p : ℕ) [Fact p.Prime] := ℚ_[p]

/-- In the coordinate order (x+3D,x-D), the four torsion values. -/
def TorsionValues (A B D : Qp p) : Prop :=
  (SqEq A 1 ∧ SqEq B 1) ∨ (SqEq A D ∧ SqEq B 1) ∨
  (SqEq A 3 ∧ SqEq B (-D)) ∨ (SqEq A (3*D) ∧ SqEq B (-D))

private theorem strip {C L V r : Qp p} (h : SqEq C L) (rn : r≠0) (eq : L=V*r^2) :
    SqEq C V := h.trans ⟨r,rn,eq⟩

theorem root_balls (p2 : p ≠ 2) (p3 : p ≠ 3) {D A B x u v w : Qp p} (dn : D≠0)
    (E : x=A*B*u^2) (F : x-D=B*v^2) (G : x+3*D=A*w^2) :
    TorsionValues A B D ∨ (‖x‖=‖D‖ ∧ ‖x-D‖=‖D‖ ∧ ‖x+3*D‖=‖D‖ ∧
      IsSquare (x*(x-D)*(x+3*D)) ∧ SqEq A (x+3*D) ∧ SqEq B (x-D)) := by
  have t2 : (2:Qp p)≠0 := by norm_num
  have t3 : (3:Qp p)≠0 := by norm_num
  have n3 : ‖(3:Qp p)‖=1 := by
    apply padic_norm_intCast_eq_one (c:=3)
    intro h
    have pp : p ∣ 3 := by exact_mod_cast h
    exact p3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp pp)
  have n3D : ‖3*D‖=‖D‖ := by rw [norm_mul,n3,one_mul]
  have n4D : ‖(4:Qp p)*D‖=‖D‖ := by
    rw [show (4:Qp p)=2^2 by norm_num,norm_mul,norm_pow,padic_norm_two p2,one_pow,one_mul]
  have d4 : (4:Qp p)*D≠0 := mul_ne_zero (by norm_num) dn
  rcases lt_trichotomy ‖x‖ ‖D‖ with low|eq|high
  · have y : SqEq (x-D) (-D) := by
      rw [show x-D= -D+x by ring];exact sqEq_add_of_norm_lt p2 (by rwa [norm_neg])
    have z : SqEq (x+3*D) (3*D) := by
      rw [add_comm];exact sqEq_add_of_norm_lt p2 (by rwa [n3D])
    exact Or.inl (Or.inr (Or.inr (Or.inr ⟨class_of_equation G (mul_ne_zero t3 dn) z,
      class_of_equation F (neg_ne_zero.mpr dn) y⟩)))
  · have xn : x≠0 := norm_pos_iff.mp (eq.symm ▸ norm_pos_iff.mpr dn)
    by_cases small : ‖x-D‖ < ‖D‖
    · have sx : SqEq x D := by
        rw [show x=D+(x-D) by ring];exact sqEq_add_of_norm_lt p2 small
      have sz : SqEq (x+3*D) (4*D) := by
        rw [show x+3*D = 4*D+(x-D) by ring];exact sqEq_add_of_norm_lt p2 (by rwa [n4D])
      have ax : SqEq A D := strip (class_of_equation G d4 sz) t2 (by ring)
      have ab : SqEq (B*A) D := by rw [mul_comm]; exact class_of_equation E dn sx
      have bb := sqEq_of_mul_sqEq ab ax dn
      exact Or.inl (Or.inr (Or.inl ⟨ax,strip bb dn (by ring)⟩))
    by_cases small3 : ‖x+3*D‖ < ‖D‖
    · have sx : SqEq x (-(3*D)) := by
        rw [show x= -(3*D)+(x+3*D) by ring]
        exact sqEq_add_of_norm_lt p2 (by rwa [norm_neg,n3D])
      have sy : SqEq (x-D) (-(4*D)) := by
        rw [show x-D= -(4*D)+(x+3*D) by ring]
        exact sqEq_add_of_norm_lt p2 (by rwa [norm_neg,n4D])
      have bb : SqEq B (-D) := strip (class_of_equation F (neg_ne_zero.mpr d4) sy) t2 (by ring)
      have ab := class_of_equation E (neg_ne_zero.mpr (mul_ne_zero t3 dn)) sx
      have aa := sqEq_of_mul_sqEq ab bb (neg_ne_zero.mpr dn)
      exact Or.inl (Or.inr (Or.inr (Or.inl ⟨strip aa dn (by ring),bb⟩)))
    · have sy : ‖x-D‖=‖D‖ := by
        refine le_antisymm ?_ (le_of_not_gt small)
        rw [sub_eq_add_neg];exact (Padic.nonarchimedean _ _).trans (by rw [eq,norm_neg,max_self])
      have sz : ‖x+3*D‖=‖D‖ := by
        exact le_antisymm ((Padic.nonarchimedean _ _).trans (by rw [eq,n3D,max_self])) (le_of_not_gt small3)
      have yn : x-D≠0 := norm_pos_iff.mp (sy.symm ▸ norm_pos_iff.mpr dn)
      have zn : x+3*D≠0 := norm_pos_iff.mp (sz.symm ▸ norm_pos_iff.mpr dn)
      exact Or.inr ⟨eq,sy,sz,square_product E F G,class_of_equation G zn (.refl _),class_of_equation F yn (.refl _)⟩
  · have xn : x≠0 := norm_pos_iff.mp (lt_trans (norm_pos_iff.mpr dn) high)
    have sy : SqEq (x-D) x := by
      rw [sub_eq_add_neg]; exact sqEq_add_of_norm_lt p2 (by rwa [norm_neg])
    have sz : SqEq (x+3*D) x := sqEq_add_of_norm_lt p2 (by rwa [n3D])
    have ab := class_of_equation E xn (SqEq.refl x)
    have bb := class_of_equation F xn sy
    have aa := class_of_equation G xn sz
    have oneA : SqEq A 1 := strip (sqEq_of_mul_sqEq ab bb xn) xn (by ring)
    exact Or.inl (Or.inl ⟨oneA,bb.trans (aa.symm.trans oneA)⟩)

end Sun28.MarkedOdd
#print axioms Sun28.MarkedOdd.root_balls
