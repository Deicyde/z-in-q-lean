import LocalMultiplication

namespace StructuralReduction
open Lean.Grind WitnessTransfer BinaryQuartic
attribute [local instance] Semiring.natCast Ring.intCast

variable {K : Type} [Field K]

private theorem cancel {m a b : K} (nz : m≠0) (same : m*a=m*b) : a=b :=
  cancel_unit ⟨m⁻¹,Field.inv_mul_cancel nz⟩ same

/-- Literal affine curve coordinates, the reciprocal and the parameter -x/y. -/
structure AffineValue (D z : K) where
  x : K
  y : K
  f : K
  finite : f*x=1
  curve : y^2=x^3-D*x
  parameter : z*y= -x

theorem AffineValue.live {D z : K} (a : AffineValue D z) : a.f≠0 ∧ a.x≠0 ∧ z≠0 := by
  have f : a.f≠0 := by intro h;have e:=a.finite;rw [h,Semiring.zero_mul] at e;exact Field.zero_ne_one e
  have x : a.x≠0 := by intro h;have e:=a.finite;rw [h,Semiring.mul_zero] at e;exact Field.zero_ne_one e
  refine ⟨f,x,?_⟩;intro h;apply x
  have e:=a.parameter;grobner

private theorem AffineValue.ordinate {D z : K} (a : AffineValue D z) :
    z*(a.x^2-D)= -a.y := by
  apply cancel a.live.2.1
  calc a.x*(z*(a.x^2-D))=z*(a.x^3-D*a.x) := by grobner
       _=(z*a.y)*a.y := by rw [←a.curve];grobner
       _=a.x*(-a.y) := by rw [a.parameter];grobner

theorem AffineValue.reciprocal {D z : K} (a : AffineValue D z) :
    a.f=z^2*(1-D*a.f^2) := by
  have fx := a.finite
  have eq : a.x=z^2*(a.x^2-D) := by
    calc a.x= -z*a.y := by have h:=a.parameter;grobner
         _=z*(z*(a.x^2-D)) := by rw [a.ordinate];grobner
         _=_ := by grobner
  calc a.f = a.x*a.f^2 := by have e:=congrArg (·*a.f) fx;grobner
       _=(z^2*(a.x^2-D))*a.f^2 := congrArg (·*a.f^2) eq
       _=z^2*(1-D*a.f^2) := by
          have e : (a.x*a.f)^2=1 := by rw [CommSemiring.mul_comm,a.finite];grobner
          calc _=z^2*((a.x*a.f)^2-D*a.f^2) := by grobner
               _=_ := by rw [e]

/-- The ordinary tangent and its doubled abscissa give the exact squared reciprocal
formula, valid on both branches of the input point. -/
theorem double_reciprocal {D z z₂ : K} (a : AffineValue D z) (b : AffineValue D z₂) (slope : K)
    (tangent : 2*a.y*slope=3*a.x^2-D) (doubleX : b.x=slope^2-2*a.x) :
    b.f*(1+D*a.f^2)^2=4*z^2*(1-D*a.f^2)^2 := by
  have dx : (4*a.y^2)*b.x=(a.x^2+D)^2 := by
    calc _=(2*a.y*slope)^2-8*a.y^2*a.x := by rw [doubleX];grobner
         _=_ := by rw [tangent,a.curve];grobner
  have recip : b.f*(a.x^2+D)^2=4*a.y^2 := by
    calc _=(b.f*b.x)*(4*a.y^2) := by rw [←dx];grobner
         _=_ := by rw [b.finite];grobner
  have fx : (a.x*a.f)^2=1 := by rw [CommSemiring.mul_comm,a.finite];grobner
  have plus : a.x^2*(1+D*a.f^2)=a.x^2+D := by
    calc _ = a.x^2+D*(a.x*a.f)^2 := by grobner
         _ = _ := by rw [fx];grobner
  have minus : a.x^2*(1-D*a.f^2)=a.x^2-D := by
    calc _ = a.x^2-D*(a.x*a.f)^2 := by grobner
         _ = _ := by rw [fx];grobner
  have xnz:=a.live.2.1
  have xu : a.x^2≠0 := by
    intro e
    have z : a.x*a.x=0 := by grobner
    exact (Field.of_mul_eq_zero z).elim xnz xnz
  have xx : a.x^2*a.x^2≠0 := fun e=>(Field.of_mul_eq_zero e).elim xu xu
  apply cancel xx
  calc _=b.f*(a.x^2*(1+D*a.f^2))^2 := by grobner
       _=4*a.y^2 := by rw [plus,recip]
       _=4*(z*(a.x^2*(1-D*a.f^2)))^2 := by rw [minus,a.ordinate];grobner
       _=_ := by grobner

variable {p : Nat} (w : ExtensionPlace p K)

private theorem sq_value {x : K} (nz : x≠0) : x^2≠0 ∧ w.val (x^2)=2*w.val x := by
  have h:=w.product nz nz
  rw [show x^2=x*x by grobner];exact ⟨h.1,by rw [h.2];omega⟩

private theorem const_value (hp : Prime p) (i : Nat) (live : 0<i) (unit : ¬p∣i) :
    (i:K)≠0 ∧ w.val (i:K)=0 := by
  have h := w.on_int (n:=(i:Int)) (by omega)
  rw [Ring.intCast_natCast,Rat.intCast_natCast,order_nat_unit hp unit] at h;exact h

private theorem one_value (hp : Prime p) : (1:K)≠0 ∧ w.val 1=0 := by
  simpa only [Semiring.natCast_one] using const_value w hp 1 (by decide) (fun d => by have := Nat.eq_one_of_dvd_one d;have := hp.1;omega)

private theorem signs {x : K} (hp : Prime p) (difference : x≠0 → w.val x≠0) :
    1+x≠0 ∧ 1-x≠0 ∧ w.val (1+x)=w.val (1-x) := by
  obtain ⟨one,vo⟩:=one_value w hp
  by_cases zx : x=0
  · rw [zx,show (1:K)+0=1 by grobner,show (1:K)-0=1 by grobner];exact ⟨one,one,rfl⟩
  have zn : -x≠0 := by intro e;apply zx;grobner
  have vneg:=w.neg x zx
  have vne:=difference zx
  have a:=w.addUnequal 1 x one zx (by omega)
  have b:=w.addUnequal 1 (-x) one zn (by omega)
  rw [show (1:K)-x=1+(-x) by grobner]
  exact ⟨a.1,b.1,by rw [a.2,b.2,vneg]⟩

private theorem integral_product {a b : K} (va : w.deep 0 a) (vb : w.deep 0 b) : w.deep 0 (a*b) := by
  intro nz
  have al : a≠0 := fun z=>nz (by rw [z,Semiring.zero_mul])
  have bl : b≠0 := fun z=>nz (by rw [z,Semiring.mul_zero])
  have := va al;have := vb bl;rw [w.mul _ _ al bl];omega

private theorem integral_neg {a : K} (ha : w.deep 0 a) : w.deep 0 (-a) := by
  intro nz
  have al : a≠0 := fun z=>nz (by rw [z];grobner)
  rw [w.neg a al];exact ha al

theorem curve_coeffs (hp : Prime p) (large : 5≤p) {rho : K} (root : rho^2=2) :
    rho≠0 ∧ w.val rho=0 ∧ w.deep 0 ((3-rho)^2) := by
  have small (i : Nat) (lt : i<p) (pos : 0<i) : ¬p∣i := fun d=>Nat.not_lt_of_ge (Nat.le_of_dvd pos d) lt
  obtain ⟨t2,v2⟩:=const_value w hp 2 (by decide) (small 2 (by omega) (by decide))
  have v3:=(const_value w hp 3 (by decide) (small 3 (by omega) (by decide))).2
  rw [←Semiring.ofNat_eq_natCast 2] at t2 v2
  rw [←Semiring.ofNat_eq_natCast 3] at v3
  have nz : rho≠0 := by intro z;apply t2;rw [←root,z];grobner
  have sq:=(sq_value w nz).2
  rw [root] at sq
  have vr : w.val rho=0 := by change w.val 2=0 at v2;omega
  have d3 : w.deep 0 (3:K) := fun _=>Int.le_of_eq v3.symm
  have dr : w.deep 0 rho := fun _=>Int.le_of_eq vr.symm
  have ds : w.deep 0 (3-rho) := by rw [show (3:K)-rho=3+(-rho) by grobner];exact w.deep_add d3 (integral_neg w dr)
  exact ⟨nz,vr,by rw [show (3-rho)^2=(3-rho)*(3-rho) by grobner];exact integral_product w ds ds⟩

private theorem w_value {D f : K} (hD : w.deep 0 D) (fz : f≠0) (nz : D*f^2≠0) :
    2*w.val f ≤ w.val (D*f^2) := by
  have dn : D≠0 := fun z=>nz (by rw [z,Semiring.zero_mul])
  obtain ⟨nn,eq⟩:=sq_value w fz
  have := hD dn
  rw [w.mul _ _ dn nn,eq];omega

theorem formal_parameter (hp : Prime p) {D z : K} (d : w.deep 0 D) (a : AffineValue D z)
    (pos : 0<w.val a.f) : w.val a.f=2*w.val z := by
  obtain ⟨one,vo⟩:=one_value w hp
  have A:=a.reciprocal
  let t:=D*a.f^2
  have dominant : -t≠0 → w.val (1:K)<w.val (-t) := by
    intro nz
    have tn : t≠0 := fun e=>nz (by rw [e];grobner)
    have h:=w_value w d a.live.1 tn
    rw [w.neg t tn,vo];change 0<w.val (D*a.f^2);omega
  obtain ⟨un,vu⟩:=w.dominates one dominant
  rw [show (1:K)+ -t=1-D*a.f^2 by dsimp [t];grobner] at un vu
  obtain ⟨nn,eq⟩:=sq_value w a.live.2.2
  have out:=w.mul (z^2) (1-D*a.f^2) nn un
  rw [←A,eq,vu,vo,Int.add_zero] at out
  exact out

/-- A deep z(R) can lie above either zero or infinity of the x-coordinate.
The signed factors give equal order on both branches. The tangent itself shows
that 2R is at infinity and has the same parameter depth. -/
theorem double_parameter (hp : Prime p) (large : 5≤p) {D z z₂ : K} (d : w.deep 0 D)
    (a : AffineValue D z) (b : AffineValue D z₂) (slope : K)
    (tangent : 2*a.y*slope=3*a.x^2-D) (doubleX : b.x=slope^2-2*a.x) (deep : 0<w.val z) :
    0<w.val b.f ∧ w.val z₂=w.val z := by
  let t:=D*a.f^2
  have q:=a.reciprocal
  change a.f=z^2*(1-t) at q
  have un : 1-t≠0 := fun eq=>a.live.1 (by rw [q,eq,Semiring.mul_zero])
  obtain ⟨zn,vz⟩:=sq_value w a.live.2.2
  have ne (tn : t≠0) : w.val t≠0 := by
    intro zero
    have wbound:=w_value w d a.live.1 tn
    change 2*w.val a.f≤w.val t at wbound
    have ut : w.deep 0 t := fun _=>Int.le_of_eq zero.symm
    have on : w.deep 0 (1:K) := fun _=>Int.le_of_eq (one_value w hp).2.symm
    have minu := w.deep_add on (integral_neg w ut)
    have sub : 0≤w.val (1-t) := by rw [show (1:K)-t=1+(-t) by grobner] at un ⊢;exact minu un
    have h:=w.mul (z^2) (1-t) zn un
    rw [←q,vz] at h;omega
  obtain ⟨plus,minus,same⟩:=signs w hp ne
  obtain ⟨p2,op⟩:=sq_value w plus
  obtain ⟨m2,om⟩:=sq_value w minus
  have no4 : ¬p∣4 := fun dd=>by have := Nat.le_of_dvd (by decide : 0<4) dd;omega
  obtain ⟨n4,o4⟩:=const_value w hp 4 (by decide) no4
  rw [←Semiring.ofNat_eq_natCast 4] at n4 o4
  have four : (4:K)≠0:=n4
  have four0 : w.val (4:K)=0:=o4
  have eq:=congrArg w.val (double_reciprocal a b slope tangent doubleX)
  change w.val (b.f*(1+t)^2)=w.val (4*z^2*(1-t)^2) at eq
  rw [w.mul _ _ b.live.1 p2,w.mul _ _ (w.product four zn).1 m2,w.mul _ _ four zn,op,om,vz,four0,same] at eq
  have pos : 0<w.val b.f := by omega
  have f₂:=formal_parameter w hp d b pos
  exact ⟨pos,by omega⟩

end StructuralReduction
