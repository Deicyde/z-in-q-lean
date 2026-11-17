import JointSlopeHeight
import LogBudget

namespace HeightSpecialization.Analytic
open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K]

/-- Coordinates of the primitive projective representative used in `jointHeight`. -/
def tripleDen (a b : Rat) : Nat := Nat.lcm a.den b.den
def tripleNum (d : Nat) (a : Rat) : Int := ((d/a.den:Nat):Int)*a.num

def embedRat (a : Rat) : K := (a.num:K)/(a.den:K)

def quadConstant (m n : Int) : Int := m^2-2*n^2

def quadContent (d : Nat) (m n : Int) := Nat.gcd (d^2) (Nat.gcd (2*d*m.natAbs) (quadConstant m n).natAbs)

def primitiveConstant (d : Nat) (m n : Int) := (quadConstant m n).natAbs / quadContent d m n

noncomputable def realFactor (d : Nat) (x : K) : K := bigger (d:K) (bigger x (-x))
noncomputable def archProduct (d : Nat) (m n : Int) (r : K) : K :=
  realFactor d ((m:K)+(n:K)*r)*realFactor d ((m:K)-(n:K)*r)

theorem triple_bounds (a b : Rat) :
    let d:=tripleDen a b
    let J:=jointHeight a b
    0<d ∧ d≤J ∧ (tripleNum d a).natAbs≤J ∧ (tripleNum d b).natAbs≤J := by
  dsimp only
  have pos:=Nat.lcm_pos a.den_pos b.den_pos
  have coords:=Nat.le_max_right (tripleDen a b)
    (max (tripleDen a b/a.den*a.num.natAbs) (tripleDen a b/b.den*b.num.natAbs))
  simp only [tripleNum,Int.natAbs_mul,Int.natAbs_natCast]
  exact ⟨pos,Nat.le_max_left ..,(Nat.le_trans (Nat.le_max_left ..) coords),Nat.le_trans (Nat.le_max_right ..) coords⟩

theorem scaled_coordinate (a : Rat) (d : Nat) (clear : a.den∣d) :
    embedRat (K:=K) a*(d:K)=(tripleNum d a:K) := by
  have p : (0:K)<(a.den:K) := OrderedRing.pos_natCast_of_pos _ a.den_pos
  have rep : (d:K)=((d/a.den:Nat):K)*(a.den:K) := by
    rw [←Semiring.natCast_mul,Nat.div_mul_cancel clear]
  have div : embedRat a*(a.den:K)=(a.num:K) := Field.div_mul_cancel (Preorder.ne_of_gt p)
  rw [rep,tripleNum,Ring.intCast_mul,Ring.intCast_natCast]
  calc _=(embedRat a*(a.den:K))*((d/a.den:Nat):K) := by grobner
       _=_ := by rw [div,CommSemiring.mul_comm]

private theorem positive_factor (d : Nat) (x : K) (pos : 0<d) (dominates : (d:K)≤x) :
    realFactor d x=x := by
  have p:=OrderedRing.pos_natCast_of_pos (R:=K) _ pos
  classical
  have inner : bigger x (-x)=x := by unfold bigger;split <;> grind
  unfold realFactor
  rw [inner]
  unfold bigger
  rw [if_pos dominates]

omit [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K] in
private theorem cast_square (x : Int) : (x:K)^2=((x.natAbs^2:Nat):K) := by
  have eq : ((x.natAbs^2:Nat):Int)=x^2 := by
    rw [←Int.natAbs_pow]
    exact Int.natAbs_of_nonneg (Int.sq_nonnneg x)
  have h:=congrArg (fun a:Int=>(a:K)) eq
  simpa only [Ring.intCast_natCast,Ring.intCast_pow] using h.symm

/-- If the finite denominator is below both real conjugates, the two archimedean
maxima have product equal to the quadratic norm. Its upper bound has constant one. -/
theorem positive_arch_product (d J : Nat) (m n : Int) (r : K) (sqrtTwo : r^2=2)
    (dp : 0<d) (mJ : m.natAbs≤J)
    (plus : (d:K)≤(m:K)+(n:K)*r) (minus : (d:K)≤(m:K)-(n:K)*r) :
    archProduct d m n r=(quadConstant m n:K) ∧ 0<archProduct d m n r ∧ archProduct d m n r≤((J^2:Nat):K) := by
  have x0:=OrderedRing.pos_natCast_of_pos (R:=K) _ dp
  have xp:=Preorder.lt_of_lt_of_le x0 plus
  have yp:=Preorder.lt_of_lt_of_le x0 minus
  unfold archProduct
  rw [positive_factor _ _ dp plus,positive_factor _ _ dp minus]
  have norm : ((m:K)+(n:K)*r)*((m:K)-(n:K)*r)=(m:K)^2-2*(n:K)^2 := by
    calc _=(m:K)^2-(n:K)^2*r^2 := by grobner
         _=_ := by rw [sqrtTwo];grobner
  have cap:=(OrderedRing.natCast_le_natCast_of_le (R:=K) _ _ (Nat.pow_le_pow_left mJ 2))
  rw [←cast_square m] at cap
  have square:=OrderedRing.sq_nonneg (a:=(n:K))
  refine ⟨?_,OrderedRing.mul_pos xp yp,?_⟩
  · unfold quadConstant
    rw [Ring.intCast_sub,Ring.intCast_mul,Ring.intCast_pow,Ring.intCast_pow,norm]
    grind
  · rw [norm]
    grind

private theorem physical_places (a b : Rat) (r : K)
    (plus : 1≤embedRat a+embedRat b*r) (minus : 1≤embedRat a-embedRat b*r) :
    let d:=tripleDen a b
    let m:=tripleNum d a
    let n:=tripleNum d b
    (d:K)≤(m:K)+(n:K)*r ∧ (d:K)≤(m:K)-(n:K)*r := by
  dsimp only
  let d:=tripleDen a b
  have p:=OrderedRing.natCast_nonneg (R:=K) (a:=d)
  have h:=OrderedRing.mul_le_mul_of_nonneg_right plus p
  have k:=OrderedRing.mul_le_mul_of_nonneg_right minus p
  have m:=scaled_coordinate (K:=K) a d (Nat.dvd_lcm_left ..)
  have n:=scaled_coordinate (K:=K) b d (Nat.dvd_lcm_right ..)
  change (d:K)≤(tripleNum d a:K)+(tripleNum d b:K)*r ∧ (d:K)≤(tripleNum d a:K)-(tripleNum d b:K)*r
  have pe : (embedRat a+embedRat b*r)*(d:K)=(tripleNum d a:K)+(tripleNum d b:K)*r := by
    calc _=embedRat a*(d:K)+(embedRat b*(d:K))*r := by grobner
         _=_ := by rw [m,n]
  have me : (embedRat a-embedRat b*r)*(d:K)=(tripleNum d a:K)-(tripleNum d b:K)*r := by
    calc _=embedRat a*(d:K)-(embedRat b*(d:K))*r := by grobner
         _=_ := by rw [m,n]
  rw [Semiring.one_mul,pe] at h
  rw [Semiring.one_mul,me] at k
  exact ⟨h,k⟩

theorem positive_joint_product (a b : Rat) (r : K) (sqrtTwo : r^2=2)
    (plus : 1≤embedRat a+embedRat b*r) (minus : 1≤embedRat a-embedRat b*r) :
    let d:=tripleDen a b
    let m:=tripleNum d a
    let n:=tripleNum d b
    archProduct d m n r=(quadConstant m n:K) ∧ 0<archProduct d m n r ∧
      archProduct d m n r≤(((jointHeight a b)^2:Nat):K) := by
  obtain ⟨p,_,m,_⟩:=triple_bounds a b
  obtain ⟨u,v⟩:=physical_places a b r plus minus
  exact positive_arch_product _ _ _ _ _ sqrtTwo p m u v

theorem positive_joint_log_upper (l : LogLaw K) (a b : Rat) (r hC : K) (sqrtTwo : r^2=2)
    (plus : 1≤embedRat a+embedRat b*r) (minus : 1≤embedRat a-embedRat b*r)
    (finite : 2*hC≤l.log (archProduct (tripleDen a b) (tripleNum (tripleDen a b) a) (tripleNum (tripleDen a b) b) r)) :
    hC≤l.log ((jointHeight a b:Nat):K) := by
  obtain ⟨_,pos,bound⟩:=positive_joint_product a b r sqrtTwo plus minus
  obtain ⟨d,cap,_,_⟩:=triple_bounds a b
  have J:=OrderedRing.pos_natCast_of_pos (R:=K) _ (Nat.lt_of_lt_of_le d cap)
  have lim:=l.monotone pos bound
  rw [Semiring.natCast_pow,l.power J] at lim
  grind

theorem quad_content (d : Nat) (m n : Int) (dp : 0<d) :
    let g:=quadContent d m n
    0<g ∧ g∣d^2 ∧ g∣2*d*m.natAbs ∧ g∣(quadConstant m n).natAbs := by
  let h := Nat.gcd (2*d*m.natAbs) (quadConstant m n).natAbs
  have sub : quadContent d m n∣h := Nat.gcd_dvd_right ..
  exact ⟨Nat.gcd_pos_of_pos_left h (Nat.pow_pos dp), Nat.gcd_dvd_left ..,
    Nat.dvd_trans sub (Nat.gcd_dvd_left ..),Nat.dvd_trans sub (Nat.gcd_dvd_right ..)⟩

/-- Dividing the absolute coefficients of (dX−m)²−2n² by their content yields a
primitive quadratic, including the double rational root when n=0. -/
theorem primitive_quadratic (d : Nat) (m n : Int) (dp : 0<d) :
    let g:=quadContent d m n
    Nat.gcd (d^2/g) (Nat.gcd (2*d*m.natAbs/g) ((quadConstant m n).natAbs/g))=1 := by
  obtain ⟨gp,head,mid,last⟩:=quad_content d m n dp
  dsimp only
  rw [Nat.gcd_div mid last,Nat.gcd_div head (Nat.dvd_gcd mid last)]
  exact Nat.div_self gp

theorem positive_primitive_constant (d J : Nat) (m n : Int) (r : K) (sqrtTwo : r^2=2)
    (dp : 0<d) (mJ : m.natAbs≤J) (plus : (d:K)≤(m:K)+(n:K)*r) (minus : (d:K)≤(m:K)-(n:K)*r) :
    0<primitiveConstant d m n ∧ primitiveConstant d m n≤J^2 ∧
      ((primitiveConstant d m n:Nat):K)*((quadContent d m n:Nat):K)=(quadConstant m n:K) := by
  obtain ⟨norm,pos,bound⟩:=positive_arch_product d J m n r sqrtTwo dp mJ plus minus
  rw [norm] at pos bound
  let q:=quadConstant m n
  have qpos : 0<q := by
    apply Int.lt_of_not_ge
    intro neg
    have h : (q:K)≤0 := OrderedRing.nonpos_intCast_of_nonpos _ neg
    change 0<(q:K) at pos
    grind
  have abs : ((q.natAbs:Nat):K)=(q:K) := by
    have h:=congrArg (fun i:Int=>(i:K)) (Int.natAbs_of_nonneg (Int.le_of_lt qpos))
    simpa only [Ring.intCast_natCast] using h
  have qBound : q.natAbs≤J^2 := by
    apply Nat.le_of_not_gt
    intro bad
    have clash:=(OrderedRing.natCast_lt_natCast_of_lt (R:=K) _ _ bad)
    rw [abs] at clash
    change (q:K)≤_ at bound
    grind
  obtain ⟨gp,_,_,div⟩:=quad_content d m n dp
  have absPos:=Int.natAbs_pos.mpr (Int.ne_of_gt qpos)
  refine ⟨Nat.div_pos (Nat.le_of_dvd absPos div) gp, Nat.le_trans (Nat.div_le_self ..) qBound,?_⟩
  unfold primitiveConstant
  rw [←Semiring.natCast_mul,Nat.div_mul_cancel div]
  exact abs

/-- On the expanding real branches, the primitive leading coefficient times the
product of the two roots equals the positive primitive constant term. -/
theorem positive_mahler (d J : Nat) (m n : Int) (r : K) (sqrtTwo : r^2=2)
    (dp : 0<d) (mJ : m.natAbs≤J) (plus : (d:K)≤(m:K)+(n:K)*r) (minus : (d:K)≤(m:K)-(n:K)*r) :
    let g:=quadContent d m n
    let x:=((m:K)+(n:K)*r)/(d:K)
    let y:=((m:K)-(n:K)*r)/(d:K)
    (((d^2/g:Nat):K)*x*y=((primitiveConstant d m n:Nat):K)) ∧ primitiveConstant d m n≤J^2 := by
  obtain ⟨_,bound,constant⟩:=positive_primitive_constant d J m n r sqrtTwo dp mJ plus minus
  obtain ⟨gp,lead,_,_⟩:=quad_content d m n dp
  dsimp only
  refine ⟨?_,bound⟩
  let g:=quadContent d m n
  let L:=d^2/g
  let C:=primitiveConstant d m n
  let x:=((m:K)+(n:K)*r)/(d:K)
  let y:=((m:K)-(n:K)*r)/(d:K)
  have raw : (L:K)*(g:K)=(d:K)^2 := by
    rw [←Semiring.natCast_mul,Nat.div_mul_cancel lead,Semiring.natCast_pow]
  have dpK:=OrderedRing.pos_natCast_of_pos (R:=K) _ dp
  have gK:=OrderedRing.pos_natCast_of_pos (R:=K) _ gp
  have ax : x*(d:K)=(m:K)+(n:K)*r := Field.div_mul_cancel (Preorder.ne_of_gt dpK)
  have ay : y*(d:K)=(m:K)-(n:K)*r := Field.div_mul_cancel (Preorder.ne_of_gt dpK)
  obtain ⟨norm,_,_⟩:=positive_arch_product d J m n r sqrtTwo dp mJ plus minus
  unfold archProduct at norm
  rw [positive_factor _ _ dp plus,positive_factor _ _ dp minus] at norm
  have eq : ((L:K)*x*y)*(g:K)=(C:K)*(g:K) := by
    calc _=((L:K)*(g:K))*(x*y) := by grobner
         _=(d:K)^2*(x*y) := by rw [raw]
         _=(x*(d:K))*(y*(d:K)) := by grobner
         _=(quadConstant m n:K) := by rw [ax,ay,norm]
         _=_ := constant.symm
  have cancel:=congrArg (fun a:K=>a*(g:K)⁻¹) eq
  change (((L:K)*x*y)*(g:K))*(g:K)⁻¹=((C:K)*(g:K))*(g:K)⁻¹ at cancel
  have inv : (g:K)*(g:K)⁻¹=1 := Field.mul_inv_cancel (Preorder.ne_of_gt gK)
  rw [Semiring.mul_assoc ((L:K)*x*y),Semiring.mul_assoc (C:K),inv,Semiring.mul_one,Semiring.mul_one] at cancel
  exact cancel

theorem positive_mahler_log_upper (l : LogLaw K) (a b : Rat) (r hC : K) (sqrtTwo : r^2=2)
    (plus : 1≤embedRat a+embedRat b*r) (minus : 1≤embedRat a-embedRat b*r)
    (height : let d:=tripleDen a b
      2*hC=l.log ((primitiveConstant d (tripleNum d a) (tripleNum d b):Nat):K)) :
    hC≤l.log ((jointHeight a b:Nat):K) := by
  obtain ⟨dp,dJ,mJ,_⟩:=triple_bounds a b
  obtain ⟨u,v⟩:=physical_places a b r plus minus
  obtain ⟨cm,limit,_⟩:=positive_primitive_constant _ _ _ _ r sqrtTwo dp mJ u v
  have up:=l.monotone (OrderedRing.pos_natCast_of_pos (R:=K) _ cm) (OrderedRing.natCast_le_natCast_of_le _ _ limit)
  rw [Semiring.natCast_pow,l.power (OrderedRing.pos_natCast_of_pos _ (Nat.lt_of_lt_of_le dp dJ))] at up
  dsimp only at height
  grind

/-- Absolute logarithmic height written via the primitive quadratic Mahler measure
on the branch where both real conjugates are at least one. -/
noncomputable def positiveQuadraticHeight (l : LogLaw K) (a b : Rat) : K :=
  let d:=tripleDen a b
  l.log ((primitiveConstant d (tripleNum d a) (tripleNum d b):Nat):K)/2

theorem explicit_height_le_joint (l : LogLaw K) (a b : Rat) (r : K) (sqrtTwo : r^2=2)
    (plus : 1≤embedRat a+embedRat b*r) (minus : 1≤embedRat a-embedRat b*r) :
    positiveQuadraticHeight l a b≤l.log ((jointHeight a b:Nat):K) := by
  apply positive_mahler_log_upper l a b r _ sqrtTwo plus minus
  dsimp only [positiveQuadraticHeight]
  rw [CommSemiring.mul_comm (2:K),Field.div_mul_cancel (by grind)]

/-- A rational parameter gives the square of its primitive linear polynomial. -/
theorem rational_double_root (a : Rat) :
    let d:=tripleDen a 0
    let m:=tripleNum d a
    let n:=tripleNum d 0
    d=a.den ∧ m=a.num ∧ n=0 ∧ quadContent d m n=1 ∧ primitiveConstant d m n=a.num.natAbs^2 := by
  have d : tripleDen a 0=a.den := by simp [tripleDen]
  dsimp only
  rw [d]
  have n : tripleNum a.den 0=0 := by simp [tripleNum]
  have m : tripleNum a.den a=a.num := by simp [tripleNum,Nat.div_self a.den_pos]
  rw [n,m]
  have q : (quadConstant a.num 0).natAbs=a.num.natAbs^2 := by simp [quadConstant,Int.natAbs_pow]
  obtain ⟨_,hd,_,hq⟩:=quad_content a.den a.num 0 a.den_pos
  rw [q] at hq
  have gcd : Nat.gcd (a.den^2) (a.num.natAbs^2)=1 := Nat.Coprime.pow 2 2 a.reduced.symm
  have div:=Nat.dvd_gcd hd hq
  rw [gcd] at div
  have primitive:=Nat.eq_one_of_dvd_one div
  simp [primitiveConstant,primitive,q]

#print axioms triple_bounds
#print axioms scaled_coordinate
#print axioms positive_arch_product
#print axioms positive_joint_product
#print axioms positive_joint_log_upper
#print axioms primitive_quadratic
#print axioms positive_primitive_constant
#print axioms positive_mahler
#print axioms positive_mahler_log_upper
#print axioms explicit_height_le_joint
#print axioms rational_double_root
end HeightSpecialization.Analytic
