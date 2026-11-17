import BoundedTest

namespace VerticalOrder
open Lean.Grind StructuralReduction
attribute [local instance] Semiring.natCast Ring.intCast
variable {K : Type} [Field K]

private theorem nz_mul {x y : K} (hx : x≠0) (hy : y≠0) : x*y≠0 :=
  fun z => (Field.of_mul_eq_zero z).elim hx hy
private theorem nz_neg {x : K} (hx : x≠0) : -x≠0 := fun z=>hx (by grobner)
private theorem neg (v : Place K) {x : K} (hx : x≠0) : v.v (-x)=v.v x := by
  have eq := congrArg v.v (show (-x)*(-x)=x*x by grobner)
  rw [v.mul (nz_neg hx) (nz_neg hx),v.mul hx hx] at eq
  omega
private theorem sq (v : Place K) {x : K} (hx : x≠0) : x^2≠0 ∧ v.v (x^2)=2*v.v x := by
  rw [show x^2=x*x by grobner]; exact ⟨nz_mul hx hx, by rw [v.mul hx hx]; omega⟩

def quartic (B X S : K) := (X^2-B*S^2)*(X^2+3*(B*S^2))

private theorem paired (v : Place K) (hu : (3:K)≠0) (unit : v.v 3=0) (x y : K)
    (live : x≠0 ∨ y≠0) (dist : x≠0 → y≠0 → v.v x≠v.v y) :
    x-y≠0 ∧ x+3*y≠0 ∧ v.v (x-y)=v.v (x+3*y) := by
  by_cases hy : y=0
  · have hx := live.resolve_right (fun ne=>ne hy)
    rw [hy,show x-(0:K)=x by grobner,show x+3*(0:K)=x by grobner]
    exact ⟨hx,hx,rfl⟩
  have hy3 := nz_mul hu hy
  have vu : v.v (3*y)=v.v y := by rw [v.mul hu hy,unit,Int.zero_add]
  by_cases hx : x=0
  · rw [hx,show (0:K)-y= -y by grobner,show (0:K)+3*y=3*y by grobner]
    exact ⟨nz_neg hy,hy3,(neg v hy).trans vu.symm⟩
  have hm := v.unequal hx (nz_neg hy) (by rw [neg v hy]; exact dist hx hy)
  have hp := v.unequal hx hy3 (by rw [vu]; exact dist hx hy)
  rw [show x-y=x+(-y) by grobner]; exact ⟨hm.1,hp.1,by rw [hm.2,hp.2,neg v hy,vu]⟩

theorem quartic_even (v : Place K) (hu : (3:K)≠0) (unit : v.v 3=0)
    {B : K} (hb : B≠0) {k : Int} (odd : v.v B=2*k+1) (X S : K) (live : X≠0 ∨ S≠0) :
    quartic B X S≠0 ∧ ∃ i : Int, v.v (quartic B X S)=2*i := by
  have pair := paired v hu unit (X^2) (B*S^2)
  have atLeast : X^2≠0 ∨ B*S^2≠0 := live.elim (fun h=>Or.inl (sq v h).1)
    (fun h=>Or.inr (nz_mul hb (sq v h).1))
  have orders (hX : X^2≠0) (hS : B*S^2≠0) : v.v (X^2) ≠ v.v (B*S^2) := by
    have hx : X≠0 := fun e=>hX (by rw [e]; grobner)
    have hs : S≠0 := fun e=>hS (by rw [e]; grobner)
    rw [(sq v hx).2,v.mul hb (sq v hs).1,(sq v hs).2,odd]; omega
  obtain ⟨left,right,same⟩ := pair atLeast orders
  exact ⟨nz_mul left right, v.v (X^2-B*S^2), by unfold quartic; rw [v.mul left right,←same]; omega⟩

/-- The product relation expresses theta = 1 - W²/c. -/
theorem theta_order (v : Place K) {c W theta : K} {e : Int}
    (hc : c≠0) (ce : v.v c=e) (pos : 0<e) (hw : W≠0) (unit : v.v W=0)
    (relation : c*theta=c-W^2) : theta≠0 ∧ v.v theta= -e := by
  have ws := sq v hw
  have n := v.unequal hc (nz_neg ws.1) (by rw [neg v ws.1,ws.2,unit,ce]; omega)
  rw [show c+(-W^2)=c-W^2 by grobner,←relation] at n
  have ht : theta≠0 := fun z=>n.1 (by rw [z]; grobner)
  have ord := n.2
  rw [v.mul hc ht,neg v ws.1,ws.2,unit,ce] at ord
  exact ⟨ht,by omega⟩

/-- The same valuation excludes both slopes together on every common twist. -/
theorem no_weak_pair (v : Place K) (hu : (3:K)≠0) (unit : v.v 3=0)
    {B theta : K} (hb : B≠0) (ht : theta≠0) {k j : Int} (bo : v.v B=2*k+1)
    (to' : v.v theta=2*j+1) (X S Y T z : K) (first : X≠0 ∨ S≠0) (second : Y≠0 ∨ T≠0) :
    z^2≠theta*quartic B X S*quartic B Y T := by
  obtain ⟨hl,i,oi⟩ := quartic_even v hu unit hb bo X S first
  obtain ⟨hr,l,ol⟩ := quartic_even v hu unit hb bo Y T second
  intro eq
  have hz : z≠0 := fun h=>nz_mul (nz_mul ht hl) hr (by rw [←eq,h]; grobner)
  have h := congrArg v.v eq
  rw [(sq v hz).2,v.mul (nz_mul ht hl) hr,v.mul ht hl,oi,ol,to'] at h
  omega

end VerticalOrder
#print axioms VerticalOrder.quartic_even
#print axioms VerticalOrder.theta_order
#print axioms VerticalOrder.no_weak_pair
