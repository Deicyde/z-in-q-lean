import InfinityChord

namespace ProjectionFibres
open Lean.Grind StructuralReduction WitnessTransfer BinaryQuartic
attribute [local instance] Semiring.natCast Ring.intCast

variable {p : Nat} {K : Type} [Field K] (w : ExtensionPlace p K)

theorem deep_zero (d : Int) : w.deep d (0:K) := fun h=>False.elim (h rfl)

theorem deep_lower {x : K} {a b : Int} (h : a≤b) (hx : w.deep b x) : w.deep a x :=
  fun live=>Int.le_trans h (hx live)

theorem deep_neg {a : K} {d : Int} (ha : w.deep d a) : w.deep d (-a) := by
  intro nz
  have az : a≠0 := fun z=>nz (by rw [z];grobner)
  rw [w.neg a az];exact ha az

theorem deep_sub {a b : K} {d : Int} (ha : w.deep d a) (hb : w.deep d b) : w.deep d (a-b) := by
  rw [show a-b=a+(-b) by grobner]
  exact w.deep_add ha (deep_neg w hb)

theorem deep_mul {a b : K} {d e : Int} (ha : w.deep d a) (hb : w.deep e b) : w.deep (d+e) (a*b) := by
  intro nz
  have az : a≠0 := fun z=>nz (by rw [z,Semiring.zero_mul])
  have bz : b≠0 := fun z=>nz (by rw [z,Semiring.mul_zero])
  have := ha az;have := hb bz
  rw [w.mul _ _ az bz];omega

theorem deep_sq {a : K} {d : Int} (ha : w.deep d a) : w.deep (2*d) (a^2) := by
  rw [show 2*d=d+d by omega,show a^2=a*a by grobner]
  exact deep_mul w ha ha

private theorem one_unit : (1:K)≠0 ∧ w.val 1=0 := by
  have nz : (1:K)≠0 := fun e=>Field.zero_ne_one e.symm
  have h:=w.mul 1 1 nz nz
  rw [Semiring.one_mul] at h
  exact ⟨nz,by omega⟩

private theorem one_plus {a : K} (positive : w.deep 1 a) :
    1+a≠0 ∧ w.val (1+a)=0 := by
  obtain ⟨nz,vo⟩:=one_unit w
  have h:=w.dominates nz (fun an=>by have := positive an;omega)
  rwa [vo] at h

private theorem unit_div {a b : K} {d : Int} (ha : w.deep d a) (bn : b≠0) (unit : w.val b=0) :
    w.deep d (a/b) := by
  intro nz
  have mul:=w.product nz bn
  rw [Field.div_mul_cancel bn,unit,Int.add_zero] at mul
  rw [←mul.2];exact ha mul.1

/-- The thin chart is closed under addition, and records zeros at all depths. -/
def Layer (d : Int) (t s : K) := w.deep d t ∧ w.deep (3*d) s

/-- Both coordinates initially vanishing in the residue field implies that the
second coordinate vanishes to at least three times the order of the first. -/
theorem layer_of_reduction {D t s : K} {d : Int} (hd : 0<d) (hD : w.deep 0 D)
    (eq : OnCurve D t s) (ht : w.deep d t) (hs : w.deep 1 s) : Layer w d t s := by
  have hpartial:=deep_mul w (deep_mul w hD ht) hs
  have ⟨unit,vu⟩:=one_plus w (deep_lower w (by omega) hpartial)
  have factor : s*(1+D*t*s)=t*t*t := by unfold OnCurve at eq;grobner
  refine ⟨ht,?_⟩
  intro nz
  obtain ⟨live,v⟩:=w.product nz unit
  have bound:=deep_mul w (deep_mul w ht ht) ht
  rw [←factor] at bound
  have := bound live
  rw [vu,Int.add_zero] at v
  omega

structure ChordResult (D u v a b : K) (d : Int) where
  l : K
  k : K
  t : K
  atLeft : a=l*u+k
  atRight : b=l*v+k
  intersection : Intersections D l k u v t
  onCurve : OnCurve D t (l*t-k)
  layer : Layer w d t (l*t-k)
  error : w.deep (5*d) (t-u-v)

/-- A binary addition theorem with no local group or multiplication-series law
as input. The projective chord certificate includes diagonal and inverse pairs. -/
def chord {D u v a b : K} {d : Int} (hd : 0<d) (hD : w.deep 0 D)
    (hu : OnCurve D u a) (hv : OnCurve D v b) (P : Layer w d u a) (Q : Layer w d v b) :
    ChordResult w D u v a b d := by
  let l:=slope D u v a b
  let k:=a-l*u
  let E:=2*D*l*k/leading D l
  let h:=u+v-E
  have dsum:=w.deep_add P.2 Q.2
  have ds:=deep_mul w (deep_mul w hD Q.1) dsum
  obtain ⟨d1,vd1⟩:=one_plus w (deep_lower w (by omega) ds)
  change slopeDen D v a b≠0 at d1
  change w.val (slopeDen D v a b)=0 at vd1
  have numerator : w.deep (2*d) (slopeNum D u v a) := by
    unfold slopeNum
    have cross:=deep_mul w P.1 Q.1
    have tail:=deep_mul w hD (deep_sq w P.2)
    exact deep_sub w (w.deep_add (w.deep_add (deep_sq w Q.1) (deep_lower w (by omega) cross)) (deep_sq w P.1))
      (deep_lower w (by omega) tail)
  have dl : w.deep (2*d) l := unit_div w numerator d1 vd1
  have dk : w.deep (3*d) k := deep_sub w P.2 (deep_lower w (by omega) (deep_mul w dl P.1))
  have sq:=deep_neg w (deep_mul w hD (deep_sq w dl))
  have ⟨d2,vd2⟩:=one_plus w (deep_lower w (by omega) sq)
  rw [show 1+ -(D*l^2)=leading D l by unfold leading;grobner] at d2 vd2
  have dlk:=deep_mul w (deep_mul w hD dl) dk
  have twice : w.deep (5*d) (2*D*l*k) := by
    rw [show 2*D*l*k=D*l*k+D*l*k by grobner]
    exact deep_lower w (by omega) (w.deep_add dlk dlk)
  have de : w.deep (5*d) E := unit_div w twice d2 vd2
  have dh : w.deep d h := deep_sub w (w.deep_add P.1 Q.1) (deep_lower w (by omega) de)
  have dhs : w.deep (3*d) (l*h-k) := deep_sub w (deep_lower w (by omega) (deep_mul w dl dh)) dk
  have cert : Intersections D l k u v h := chord_factor hu hv d1 rfl rfl d2 rfl
  refine ⟨l,k,h,by dsimp [k];grobner,line_through hu hv d1,cert,third_on_curve cert,⟨dh,dhs⟩,?_⟩
  rw [show h-u-v= -E by dsimp [h];grobner]
  exact deep_neg w de

/-- The actual finite coordinates give (t,-1,s) with s=tf=-1/y. -/
theorem affine_to_chart {D t : K} (a : AffineValue D t) :
    OnCurve D t (t*a.f) ∧ (t*a.f)*a.y= -1 := by
  have f:=a.reciprocal
  have sy : (t*a.f)*a.y= -1 := by
    calc _=(t*a.y)*a.f := by grobner
         _= -(a.f*a.x) := by rw [a.parameter];grobner
         _=_ := by rw [a.finite]
  refine ⟨?_,sy⟩
  unfold OnCurve
  calc t*a.f=t*(t^2*(1-D*a.f^2)) := congrArg (t*·) f
       _=_ := by grobner

/-- A positive reciprocal identifies the formal branch for the actual ordinate.
 -/
theorem affine_layer (hp : Prime p) {D t : K} (hD : w.deep 0 D)
    (a : AffineValue D t) (positive : 0<w.val a.f) :
    0<w.val t ∧ Layer w (w.val t) t (t*a.f) := by
  have order:=formal_parameter w hp hD a positive
  have ft : w.deep (w.val t) t := fun _=>Int.le_refl _
  have ff : w.deep (w.val a.f) a.f := fun _=>Int.le_refl _
  exact ⟨by omega,ft,deep_lower w (by omega) (deep_mul w ft ff)⟩

end ProjectionFibres
