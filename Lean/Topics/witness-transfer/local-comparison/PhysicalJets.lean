import Uniformizer
import Homogeneous

namespace WitnessTransfer
open Lean.Grind IndependentIndices.ChartJets FiniteJet
attribute [local instance] Semiring.natCast Ring.intCast

inductive Parameter | raw | short | pade
namespace Parameter
def k : Parameter → Nat | .raw => 1 | .short => 3 | .pade => 10
def degree : Parameter → Nat | .raw => 0 | .short => 2 | .pade => 8
def a : Parameter → Poly | .raw => [1] | .short => IndependentIndices.ChartJets.short | .pade => pNumer
def q : Parameter → Poly | .raw => [1] | .short => [15] | .pade => pDenom
theorem fits (c : Parameter) : c.a.length≤c.degree+1 ∧ c.q.length≤c.degree+1 := by cases c <;> decide
theorem q_head (c : Parameter) : (c.q.head?.getD 0)≠0 := by cases c <;> decide

theorem residual (c : Parameter) {A : Type} [CommRing A] (w : A) :
    ∃ r : A,val w (defect c.degree c.a c.q)=w^c.k*r := by
  have h:=substitution_orders w
  cases c with
  | raw => exact ⟨_,by simpa only [k,Semiring.pow_one] using h.1⟩
  | short => exact ⟨_,h.2.1⟩
  | pade => exact ⟨_,h.2.2.1⟩
end Parameter

def unit {A : Type} [CommRing A] (x : A) := ∃ b : A,b*x=1
theorem cancel_unit {A : Type} [CommRing A] {x y u : A} (hu : unit u)
    (h : u*x=u*y) : x=y := by obtain ⟨b,hb⟩:=hu;have h1:=congrArg (fun t=>b*t) h;grobner
private theorem unit_mul {A : Type} [CommRing A] {x y : A} (hx : unit x) (hy : unit y) :
    unit (x*y) := by obtain ⟨a,ea⟩:=hx;obtain ⟨b,eb⟩:=hy;exact ⟨a*b,by grobner⟩
private theorem unit_pow {A : Type} [CommRing A] {x : A} (hx : unit x) (j : Nat) :
    unit (x^j) := by
  induction j with
  | zero => rw [Semiring.pow_zero];exact ⟨1,by grobner⟩
  | succ j ih => rw [Semiring.pow_succ];exact unit_mul ih hx

theorem pow_power {A : Type} [CommRing A] (x : A) (i j : Nat) : (x^i)^j=x^(i*j) := by
  induction j with
  | zero => rw [Nat.mul_zero,Semiring.pow_zero,Semiring.pow_zero]
  | succ j ih => rw [Semiring.pow_succ,ih,Nat.mul_succ,Semiring.pow_add]

private theorem balance {A : Type} [CommRing A] (x a b : A) (h : x*(a-b)=0) : x*a=x*b := by grobner

/-- Cleared numerator identities for the actual duplication formula and the
actual rational chart suffice in any commutative ring. -/
private theorem doubled_value {A : Type} [CommRing A] (c : Parameter)
    (z w u y j j' : A) (wcoord : (1+w)^4*y=16*w*(1-w)^2)
    (zcoord : (1-6*w+w^2)*u=2*(1-w^2))
    (jcoord : val w c.q*j=z*val w c.a) (jcoord' : val y c.q*j'=z*u*val y c.a)
    (nilp : z*w^c.k=0) (hu : unit ((1+w)^4))
    (hs : unit (1-6*w+w^2)) (hq : unit (val w c.q)) (hq' : unit (val y c.q)) :
    j'=2*j := by
  have pt : val w d*y=val w n := by rw [d_formula,n_formula];exact wcoord
  obtain ⟨r,hr⟩:=c.residual w
  rw [defect_value w y c.degree c.a c.q pt c.fits.1 c.fits.2,d_formula] at hr
  have kill : ((1+w)^4)^c.degree *
      (z*((1-w^2)*val y c.a*val w c.q-(1-6*w+w^2)*val y c.q*val w c.a))=0 := by
    calc
      _=z*(((1+w)^4)^c.degree*((1-w^2)*val y c.a*val w c.q-
        (1-6*w+w^2)*val y c.q*val w c.a)) := by grobner
      _=z*(w^c.k*r) := congrArg (fun t=>z*t) hr
      _=(z*w^c.k)*r := (Semiring.mul_assoc ..).symm
      _=0 := by rw [nilp];grobner
  have core : z*((1-w^2)*val y c.a*val w c.q-(1-6*w+w^2)*val y c.q*val w c.a)=0 :=
    cancel_unit (unit_pow hu c.degree) (by rw [kill];grobner)
  apply cancel_unit (unit_mul hs (unit_mul hq hq'))
  calc
    (1-6*w+w^2)*(val w c.q*val y c.q)*j'
       = val w c.q*((1-6*w+w^2)*u)*(z*val y c.a) := by
         rw [show val w c.q*((1-6*w+w^2)*u)*(z*val y c.a)
             = ((1-6*w+w^2)*val w c.q)*(z*u*val y c.a) from by grobner, ← jcoord']; grobner
    _ = (1-6*w+w^2)*(val w c.q*val y c.q)*(2*j) := by
      rw [zcoord,show (1-6*w+w^2)*(val w c.q*val y c.q)*(2*j)
          =2*((1-6*w+w^2)*val y c.q)*(val w c.q*j) from by grobner,jcoord]
      calc
        _=2*(z*((1-w^2)*val y c.a*val w c.q)) := by grobner
        _=2*(z*((1-6*w+w^2)*val y c.q*val w c.a)) := congrArg (fun t=>2*t) (balance _ _ _ core)
        _=_ := by grobner

section RingCoordinates
variable {K : Type} [CommRing K]

/-- The curve and tangent formulas, in the truncated short-Weierstrass coordinate.
For the physical curve D=(3−√2)^2. -/
structure CurveData (K : Type) [CommRing K] (n : Nat) where
  D : K
  w : J K (n+1)
  dup : J K (n+1)
  curve : w=con (n+1) D*(X (R:=K) (n+1))^4*(1-w)^2
  doubleW : (1+w)^4*plug (n+1) dup w=16*w*(1-w)^2
  doubleZ : (1-6*w+w^2)*dup=2*(1-w^2)

theorem head_pow (n) (a : J K (n+1)) (k : Nat) : (a^k : J K (n+1)).1=a.1^k := by
  induction k with
  | zero => rw [Semiring.pow_zero,Semiring.pow_zero,← con_one];rfl
  | succ k ih => rw [Semiring.pow_succ,Semiring.pow_succ];change (a^k : J K (n+1)).1*a.1=_;rw [ih]

theorem head_poly (n) (x : J K (n+1)) (x0 : x.1=0) (a : Poly) :
    (val x a).1=((a.head?.getD 0:Int):K) := by
  cases a with
  | nil => change ((0:Nat):K)=((0:Int):K);rw [Semiring.natCast_zero,Ring.intCast_zero]
  | cons i is => change (i:K)+x.1*(val x is).1=(i:K);rw [x0];grobner

theorem plug_val (n) (u x : J K n) (a : Poly) :
    plug n u (val x a)=val (plug n u x) a := by
  induction a with
  | nil => change plug n u 0=0;rw [← con_zero (R:=K) n,plug_con]
  | cons i a ih =>
    change plug n u (plus n (i:J K n) (times n x (val x a)))=_
    rw [plug_plus,plug_int,plug_times,ih];rfl

theorem w_head {n} (f : CurveData K n) : f.w.1=0 := by
  have h:=congrArg Prod.fst f.curve
  change f.w.1=f.D*((X (n+1):J K (n+1))^4 : J K (n+1)).1*_ at h
  rw [head_pow,show ((X (n+1):J K (n+1)).1)=0 from rfl] at h;grobner

theorem head_add (n) (a b : J K (n+1)) : (a+b).1=a.1+b.1 := rfl
theorem head_mul (n) (a b : J K (n+1)) : (a*b).1=a.1*b.1 := rfl
theorem head_sub (n) (a b : J K (n+1)) : (a-b).1=a.1-b.1 := by
  change a.1+(-1)*b.1=_;grobner
private theorem head_num (n r : Nat) : (OfNat.ofNat (α:=J K (n+1)) r).1=OfNat.ofNat r := by
  change (r:K)=OfNat.ofNat r;rw [Semiring.ofNat_eq_natCast]

theorem head_one (n) : (1 : J K (n+1)).1=(1:K) := head_num n 1
theorem head_two (n) : (2 : J K (n+1)).1=(2:K) := head_num n 2
theorem head_six (n) : (6 : J K (n+1)).1=(6:K) := head_num n 6

private theorem dup_head {n} (f : CurveData K n) : f.dup.1=2 := by
  have h:=congrArg Prod.fst f.doubleZ
  change (_*_:J K (n+1)).1=(_*_:J K (n+1)).1 at h
  simp only [head_add,head_mul,head_sub,head_one,head_two,head_six,head_pow,w_head] at h
  grobner

end RingCoordinates

variable {K : Type} [Field K] [IsCharP K 0]

theorem chart_q0 (c : Parameter) :
    ((c.q.head?.getD 0:Int):K)≠0 := by
  intro eq
  have h:=(IsCharP.intCast_eq_zero_iff (α:=K) 0 _).mp eq
  exact c.q_head (by simpa using h)

theorem physical_doubles (c : Parameter) (f : CurveData K (4*c.k)) (j : J K (4*c.k+1))
    (chart : val f.w c.q*j=X (4*c.k+1)*val f.w c.a) :
    plug (4*c.k+1) f.dup j=scale (4*c.k+1) 2 j := by
  let N:=4*c.k+1
  let z:J K N:=X N
  let y:=plug N f.dup f.w
  have hy : y.1=0 := w_head f
  have hq (v : J K N) (hz : v.1=0) : unit (val v c.q) :=
    unit_of_head N _ (fun _ => show (val v c.q).1≠0 from (head_poly _ v hz c.q) ▸ chart_q0 c)
  have h1 : unit ((1+f.w)^4) := by
    apply unit_of_head N _
    intro _
    change ((_ : J K N)^4 : J K N).1≠0
    simp only [head_pow,head_add,head_one,w_head]; intro h;grobner
  have hs : unit (1-6*f.w+f.w^2) := by
    apply unit_of_head N _
    intro _
    change (_+_ : J K N).1≠0
    simp only [head_add,head_mul,head_sub,head_pow,head_one,head_six,w_head];intro h;grobner
  have nilp : z*f.w^c.k=0 := by
    have fac : f.w = z^4*(con N f.D*(1-f.w)^2) := f.curve.trans (by change con N f.D*z^4*(1-f.w)^2=_; grobner)
    rw [fac,CommSemiring.mul_pow, pow_power]
    rw [show z*(z^(4*c.k)*(con N f.D*(1-f.w)^2)^c.k) =
      z^(4*c.k+1)*(con N f.D*(1-f.w)^2)^c.k from by rw [Semiring.pow_succ];grobner]
    rw [show z^(4*c.k+1)=0 from X_nil N];grobner
  have alt:=congrArg (plug N f.dup) chart
  change plug N f.dup (times N (val f.w c.q) j)=plug N f.dup (times N z (val f.w c.a)) at alt
  rw [plug_times,plug_times,plug_val,plug_val,show plug N f.dup z=z*f.dup from plug_X N f.dup] at alt
  have conclusion:=doubled_value c z f.w f.dup y j (plug N f.dup j)
    f.doubleW f.doubleZ chart alt nilp h1 hs (hq _ (w_head f)) (hq _ hy)
  rw [conclusion]
  change times N (con N ((2:Nat):K)) j=scale N 2 j
  rw [mul_con,← Semiring.ofNat_eq_natCast (α:=K) 2]

theorem physical_multipliers (c : Parameter) (f : CurveData K (4*c.k)) (j m : J K (4*c.k+1))
    (b : K) (slope : coeff _ m 0=b) (comm : commutes _ m f.dup)
    (chart : val f.w c.q*j=X (4*c.k+1)*val f.w c.a) :
    plug _ m j=scale _ b j := by
  apply linearizes _ m f.dup j b (dup_head f) slope _ comm (physical_doubles c f j chart)
  have hj:=congrArg Prod.fst chart
  change (val f.w c.q).1*j.1=(0:K)*(val f.w c.a).1 at hj
  rw [head_poly _ _ (w_head f) c.q] at hj
  exact (Field.of_mul_eq_zero (show ((c.q.head?.getD 0:Int):K)*j.1=0 from by grobner)).resolve_left (chart_q0 c)

#print axioms physical_doubles
#print axioms physical_multipliers
end WitnessTransfer
