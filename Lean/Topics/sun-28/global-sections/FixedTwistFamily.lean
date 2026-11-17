import Cancellation
import SourceFacts

namespace Sun28.GlobalSections
open Sun28.PairedClasses Sun28.PreparedPoles Sun28.TwistExtension Sun28.TwistRank Sun28.TwistPrimes
open ZInQ.RouteK
noncomputable section

def strictPoint (b l:ℕ) : Prop := ∃ t y:ℚ, t≠0 ∧ y≠0 ∧
    y^2=((b:ℚ)*t^2)*(b*t^2-l)*(b*t^2+3*l)

theorem strict_of_family {b d:ℕ} (bp:0<b) (dp:1<d) (sf:Squarefree d)
    (fam:Family b d) : strictPoint b (b*d) := by
  obtain ⟨t,y,tn,E⟩:=(fixed_points_of_family bp (by omega : 0<d) fam).2
  refine ⟨t,y,tn,?_,E⟩
  intro zero
  subst y
  have pos:0<(b:ℚ)*t^2:=mul_pos (by exact_mod_cast bp) (sq_pos_of_ne_zero tn)
  have dn:0<(d:ℚ):=by exact_mod_cast (by omega : 0<d)
  push_cast at E
  have plus:0<(b:ℚ)*t^2+3*((b:ℚ)*d):=by positivity
  have X:(b:ℚ)*t^2-(b:ℚ)*d=0:=
    (mul_eq_zero.mp ((mul_eq_zero.mp (by simpa using E.symm)).resolve_right plus.ne')).resolve_left pos.ne'
  have D:(d:ℚ)=t^2 := by
    apply mul_left_cancel₀ (by exact_mod_cast bp.ne' : (b:ℚ)≠0)
    linear_combination -X
  have one:=sqf_eq_of_eq_mul_sq (d:=(1:ℤ)) squarefree_one tn
    (show (d:ℚ)=(1:ℤ)*t^2 by simpa using D)
  have same:=sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr sf) (t:=(1:ℚ)) one_ne_zero
    (show (d:ℚ)=(d:ℤ)*(1:ℚ)^2 by simp)
  have bad:d=1:=by exact_mod_cast same.symm.trans one
  omega

theorem quotient_norm {b q θ:ℕ} (qp:0<q) (one:Family b q) (two:Family b (q*θ)) :
    ∃ x y:ℚ,(θ:ℚ)=x^2-(b:ℚ)*y^2 := by
  obtain ⟨u,v,e⟩:=product_norm one two
  have nz:(q:ℚ)≠0:=by exact_mod_cast qp.ne'
  refine ⟨u/q,v/q,?_⟩
  push_cast at e
  field_simp
  linear_combination e

/-- A common factor can be removed from the *target*, leaving the same fixed
strict, positive, coprime twist n on both equations. -/
theorem unbounded_fixed_twist {b:ℕ} (bp:0<b) (bs:Squarefree b) (b6:b.Coprime 6) (bm:b%24=17) :
    ∃ q:ℕ, 1<q ∧ AdmissiblePair b q ∧ Family b q ∧ FixedSquares q ∧
      Squarefree (b*q) ∧ strictPoint b (b*q) ∧
      ∀ bound:ℕ, ∃ θ:ℕ, bound<θ ∧ 1<θ ∧ AdmissiblePair b θ ∧ FixedSquares θ ∧
        NormConic b θ ∧ Family b (q*θ) ∧ (b*q).Coprime (6*θ) ∧
        strictPoint b ((b*q)*θ) ∧ Realized b θ := by
  obtain ⟨q,qp,aq,fq,fam,_⟩:=fixed_factor bp bs b6 bm (by decide : 0<1) (Nat.coprime_one_right _) 1
  have c:=aq.2.2.2.2.1
  have sq:=aq.2.2.2.1
  have sn:Squarefree (b*q):= (Nat.squarefree_mul c).mpr ⟨bs,sq⟩
  have P:=strict_of_family bp qp sq fam
  refine ⟨q,qp,aq,fam,fq,sn,P,?_⟩
  intro bound
  obtain ⟨d,bd,hit,ad,fd,famD⟩:=fixed_multiple aq fq (q*max 1 bound)
  obtain ⟨θ,rfl⟩:=hit
  have gt:max 1 bound<θ:=Nat.lt_of_mul_lt_mul_left bd
  have tb:bound<θ:=(le_max_right ..).trans_lt gt
  have gtOne:1<θ:=(le_max_left ..).trans_lt gt
  obtain ⟨atθ,qt⟩:=admissible_quotient aq ad
  have ct : (b*q).Coprime (6*θ) :=
    (b6.mul_right atθ.2.2.2.2.1).mul_left (aq.2.2.2.2.2.2.1.mul_right qt)
  have Q : strictPoint b ((b*q)*θ) := by
    rw [Nat.mul_assoc]
    exact strict_of_family bp (by nlinarith) ad.2.2.2.1 famD
  refine ⟨θ,tb,gtOne,atθ,fixed_quotient fq fd,norm_conic bp atθ.2.1 atθ.2.2.2.1 gtOne
      (quotient_norm aq.2.1 fam famD),famD,ct,Q,?_⟩
  obtain ⟨u,y,un,_,e⟩:=P
  obtain ⟨v,z,vn,_,h⟩:=Q
  exact ⟨b*q,Nat.mul_pos bp aq.2.1,sn,ct,⟨u,y,un,e⟩,⟨v,z,vn,h⟩⟩

/-- A project-specific global criterion at a single, necessarily coprime,
pair of overlapping factorizations. The square and direction families are both admitted. -/
def CancelledFactors (b θ:ℕ) : Prop :=
  ∃ q:ℕ, 1<q ∧ Squarefree (b*q) ∧ (b*q).Coprime (6*θ) ∧ Factor b q ∧ Factor b (q*θ)

theorem realized_of_cancelled {b θ:ℕ} (bp:0<b) (tp:0<θ) (h:CancelledFactors b θ) :
    Realized b θ := by
  obtain ⟨q,qp,sf,cp,one,two⟩:=h
  have qpos:0<q:=by omega
  obtain ⟨u,y,un,e⟩:=factor_point bp qpos one
  obtain ⟨v,z,vn,g⟩:=factor_point bp (Nat.mul_pos qpos tp) two
  refine ⟨b*q,Nat.mul_pos bp qpos,sf,cp,⟨u,y,un,?_⟩,⟨v,z,vn,?_⟩⟩
  · simpa only [Nat.cast_mul] using e
  · simpa only [Nat.cast_mul,mul_assoc] using g

end
end Sun28.GlobalSections
#print axioms Sun28.GlobalSections.strict_of_family
#print axioms Sun28.GlobalSections.quotient_norm
#print axioms Sun28.GlobalSections.unbounded_fixed_twist
#print axioms Sun28.GlobalSections.realized_of_cancelled
