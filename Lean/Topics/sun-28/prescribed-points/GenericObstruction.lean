import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Tactic

namespace Sun28.PrescribedPoints
open RatFunc
noncomputable section

private theorem deg_add_lt {x y : RatFunc ℚ} (xn : x≠0) (yn : y≠0)
    (d : x.intDegree<y.intDegree) : (x+y).intDegree=y.intDegree := by
  have n : x+y≠0:=by
    intro h
    have e : x= -y:=eq_neg_of_add_eq_zero_left h
    rw [e,intDegree_neg] at d
    omega
  have upper:=(intDegree_add_le yn n).trans_eq (max_eq_right d.le)
  have lower:=intDegree_add_le (neg_ne_zero.mpr xn)
    (show (x+y)+(-x)≠0 from by rwa [show x+y+ -x=y by ring])
  rw [show x+y+ -x=y by ring,intDegree_neg] at lower
  exact le_antisymm upper (by omega)

private theorem deg_add {x y : RatFunc ℚ} (xn : x≠0) (yn : y≠0)
    (d : x.intDegree≠y.intDegree) : (x+y).intDegree=max x.intDegree y.intDegree := by
  rcases lt_or_gt_of_ne d with lt|gt
  · rw [deg_add_lt xn yn lt,max_eq_right lt.le]
  · rw [add_comm,deg_add_lt yn xn gt,max_eq_left gt.le]

private theorem deg_sq (x : RatFunc ℚ) : (x^2).intDegree=2*x.intDegree := by
  by_cases h : x=0
  · simp [h]
  · rw [pow_two,intDegree_mul h h];ring

def functionQuartic (b u v : RatFunc ℚ) := (u^2-b*v^2)*(u^2+3*b*v^2)

theorem even_function_quartic {b u v : RatFunc ℚ} (bn : b≠0) (bo : Odd b.intDegree)
    (live : functionQuartic b u v≠0) : Even (functionQuartic b u v).intDegree := by
  have c : (3:RatFunc ℚ)≠0:=by norm_num
  have cd : (3:RatFunc ℚ).intDegree=0:=by
    have eq : (3:RatFunc ℚ)= RatFunc.C (3:ℚ):=by norm_num
    rw [eq,intDegree_C]
  have p:=left_ne_zero_of_mul live
  have q:=right_ne_zero_of_mul live
  unfold functionQuartic
  rw [intDegree_mul p q]
  suffices e : (u^2-b*v^2).intDegree=(u^2+3*b*v^2).intDegree by
    rw [e];exact ⟨_,rfl⟩
  by_cases hv : v=0
  · simp [hv]
  have bv := mul_ne_zero bn (pow_ne_zero 2 hv)
  have cv := mul_ne_zero (mul_ne_zero c bn) (pow_ne_zero 2 hv)
  have deg3 : (3*b*v^2).intDegree=(b*v^2).intDegree := by
    rw [intDegree_mul (mul_ne_zero c bn) (pow_ne_zero 2 hv),intDegree_mul c bn,
      cd,zero_add,intDegree_mul bn (pow_ne_zero 2 hv)]
  by_cases hu : u=0
  · simpa only [hu,zero_pow two_ne_zero,zero_sub,zero_add,intDegree_neg] using deg3.symm
  have ud := pow_ne_zero 2 hu
  have ne : (u^2).intDegree≠(b*v^2).intDegree := by
    obtain ⟨j,e⟩:=bo
    rw [intDegree_mul bn (pow_ne_zero 2 hv),deg_sq,deg_sq,e]
    omega
  rw [sub_eq_add_neg,deg_add ud (neg_ne_zero.mpr bv) (by simpa only [intDegree_neg] using ne),
    intDegree_neg,deg_add ud cv (by rwa [deg3]),deg3]

theorem no_odd_function_pair {b θ : RatFunc ℚ} (bn : b≠0) (tn : θ≠0) (bo : Odd b.intDegree)
    (to' : Odd θ.intDegree) :
    ¬∃ u v U V w : RatFunc ℚ,w≠0 ∧ w^2=θ*functionQuartic b u v*functionQuartic b U V := by
  rintro ⟨u,v,U,V,w,wn,h⟩
  have prod : θ*functionQuartic b u v*functionQuartic b U V≠0:=h ▸ pow_ne_zero 2 wn
  have first:=right_ne_zero_of_mul (left_ne_zero_of_mul prod)
  have last:=right_ne_zero_of_mul prod
  have eq:=congrArg intDegree h
  rw [deg_sq,intDegree_mul (mul_ne_zero tn first) last,intDegree_mul tn first] at eq
  obtain ⟨i,di⟩:=even_function_quartic bn bo first
  obtain ⟨j,dj⟩:=even_function_quartic bn bo last
  obtain ⟨a,da⟩:=to'
  omega

/-- The generic conic has the point (1,1), but its signed pole surface
does not have a point over the rational function field. -/
theorem generic_norm_obstruction :
    let b : RatFunc ℚ:=RatFunc.X
    let θ : RatFunc ℚ:=1-b
    b*1^2+θ*1^2=1 ∧
    ¬∃ u v U V w : RatFunc ℚ,w≠0 ∧ w^2=θ*functionQuartic b u v*functionQuartic b U V := by
  dsimp only
  have nx : (RatFunc.X:RatFunc ℚ)≠0:=RatFunc.X_ne_zero
  have d : (1-(RatFunc.X:RatFunc ℚ)).intDegree=1:=by
    rw [sub_eq_add_neg,deg_add_lt one_ne_zero (neg_ne_zero.mpr nx) (by simp),intDegree_neg,intDegree_X]
  have n : 1-(RatFunc.X:RatFunc ℚ)≠0:=by intro h; simp [h] at d
  exact ⟨by ring,no_odd_function_pair nx n (by simp) (by rw [d];decide)⟩
/-- The two literal square equations over the rational-function field. -/
def functionBranch (μ B e z : RatFunc ℚ) : Prop :=
  let a:=μ*B
  let H:=a*(a-B^2)
  a*e*H*z≠0 ∧ ∃ y w : RatFunc ℚ,
    y^2=a*(a-e)*(a+3*e) ∧ w^2=a*(a*z^2-e*H)*(a*z^2+3*(e*H))

theorem odd_twist_necessary {x l y : RatFunc ℚ} (xn : x≠0) (ln : l≠0)
    (xo : Odd x.intDegree) (h : y^2=x*(x-l)*(x+3*l)) : Odd l.intDegree := by
  by_contra no
  have c : (3:RatFunc ℚ)≠0:=by norm_num
  have cd : (3:RatFunc ℚ).intDegree=0:=by
    have eq : (3:RatFunc ℚ)= RatFunc.C (3:ℚ):=by norm_num
    rw [eq,intDegree_C]
  have d : x.intDegree≠l.intDegree:=by rintro e;exact no (e ▸ xo)
  have d3 : (3*l).intDegree=l.intDegree:=by rw [intDegree_mul c ln,cd,zero_add]
  have n : x-l≠0:=fun eq=>d (congrArg intDegree (sub_eq_zero.mp eq))
  have m : x+3*l≠0:=by
    intro e
    have rel:=congrArg intDegree (eq_neg_of_add_eq_zero_left e)
    rw [intDegree_neg,d3] at rel
    exact d rel
  have same : (x-l).intDegree=(x+3*l).intDegree:=by
    rw [sub_eq_add_neg,deg_add xn (neg_ne_zero.mpr ln) (by simpa [intDegree_neg] using d),
      intDegree_neg,deg_add xn (mul_ne_zero c ln) (by rwa [d3]),d3]
  have eq:=congrArg intDegree h
  rw [deg_sq,intDegree_mul (mul_ne_zero xn n) m,intDegree_mul xn n,same] at eq
  obtain ⟨i,t⟩:=xo
  omega

theorem no_function_branch {μ B : RatFunc ℚ} (mn : μ≠0) (mc : μ.intDegree=0)
    (bn : B≠0) (pos : 0<B.intDegree) (odd : Odd B.intDegree) :
    ¬∃ e z, functionBranch μ B e z := by
  rintro ⟨e,z,guard,y,w,h,k⟩
  let a:=μ*B
  let H:=a*(a-B^2)
  change a*e*H*z≠0 at guard
  change y^2=a*(a-e)*(a+3*e) at h
  change w^2=a*(a*z^2-e*H)*(a*z^2+3*(e*H)) at k
  have an:=mul_ne_zero mn bn
  have en:=right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul guard))
  have Hn:=right_ne_zero_of_mul (left_ne_zero_of_mul guard)
  have zn:=right_ne_zero_of_mul guard
  have ae : a.intDegree=B.intDegree:=by dsimp [a];rw [intDegree_mul mn bn,mc,zero_add]
  have diff : (a-B^2).intDegree=2*B.intDegree:=by
    rw [sub_eq_add_neg,deg_add_lt an (neg_ne_zero.mpr (pow_ne_zero 2 bn)) (by rw [ae,intDegree_neg,deg_sq];omega),
      intDegree_neg,deg_sq]
  have he : H.intDegree=3*B.intDegree:=by
    dsimp only [H];rw [intDegree_mul an (right_ne_zero_of_mul Hn),diff,ae];ring
  have i:=odd_twist_necessary an en (ae ▸ odd) h
  have j : Odd (a*z^2).intDegree:=by
    rw [intDegree_mul an (pow_ne_zero _ zn),ae,deg_sq]
    obtain ⟨t,ex⟩:=odd
    exact ⟨t+z.intDegree,by omega⟩
  have second := odd_twist_necessary (mul_ne_zero an (pow_ne_zero 2 zn)) (mul_ne_zero en Hn) j
    (show (z*w)^2=(a*z^2)*(a*z^2-e*H)*(a*z^2+3*(e*H)) by linear_combination z^2*k)
  rw [intDegree_mul en Hn,he] at second
  obtain ⟨t,ex⟩:=odd
  obtain ⟨k₁,e₁⟩:=i
  obtain ⟨k₂,e₂⟩:=second
  omega

theorem no_constant_multiplier (c : ℚ) :
    ¬∃ e z, functionBranch (RatFunc.C c) (RatFunc.X:RatFunc ℚ) e z := by
  by_cases nc : c=0
  · subst c
    simp [functionBranch]
  · exact no_function_branch (by simpa using nc) (intDegree_C c) RatFunc.X_ne_zero
      (by simp) (by simp)

end
end Sun28.PrescribedPoints
#print axioms Sun28.PrescribedPoints.even_function_quartic
#print axioms Sun28.PrescribedPoints.no_odd_function_pair
#print axioms Sun28.PrescribedPoints.generic_norm_obstruction
#print axioms Sun28.PrescribedPoints.odd_twist_necessary
#print axioms Sun28.PrescribedPoints.no_function_branch
#print axioms Sun28.PrescribedPoints.no_constant_multiplier
