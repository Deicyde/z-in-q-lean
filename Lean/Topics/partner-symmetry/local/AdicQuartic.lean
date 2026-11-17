import BinaryQuartic

namespace AdicQuartic
open Lean.Grind BinaryQuartic
open Fin.NatCast Fin.IntCast

/-- Representatives of a compatible system of residues modulo p^(n+1).
    Congruence at every level is equality of the represented p-adic integers. -/
structure Tower (p : Nat) where
  level : Nat → Int
  compat : ∀ n, (p:Int)^(n+1) ∣ level (n+1)-level n

namespace Tower

def con (p : Nat) (a : Int) : Tower p := ⟨fun _ => a,by intro n; simp⟩
def plus {p} (a b : Tower p) : Tower p :=
  ⟨fun n => a.level n+b.level n,by
    intro n
    obtain ⟨x,hx⟩ := a.compat n
    obtain ⟨y,hy⟩ := b.compat n
    exact ⟨x+y,by grobner⟩⟩
def times {p} (a b : Tower p) : Tower p :=
  ⟨fun n => a.level n*b.level n,by
    intro n
    obtain ⟨x,hx⟩ := a.compat n
    obtain ⟨y,hy⟩ := b.compat n
    exact ⟨x*b.level (n+1)+a.level n*y,by grobner⟩⟩
def opposite {p} (a : Tower p) : Tower p :=
  ⟨fun n => -a.level n,by
    intro n
    obtain ⟨x,h⟩ := a.compat n
    exact ⟨-x,by grobner⟩⟩

def sq {p} (a : Tower p) := times a a
def Equal {p} (a b : Tower p) : Prop := ∀ n, (p:Int)^(n+1) ∣ a.level n-b.level n
def Vanishes {p} (a : Tower p) : Prop := ∀ n, (p:Int)^(n+1) ∣ a.level n
def res {p} [NeZero p] (a : Tower p) : Fin p := (a.level 0 : Fin p)

theorem red_zero {p} [NeZero p] (x : Int) : (x : Fin p)=0 ↔ (p:Int)∣x := by
  rw [IsCharP.intCast_eq_zero_iff (α := Fin p) p x, Int.dvd_iff_emod_eq_zero]

theorem red_eq {p} [NeZero p] (x y : Int) : (x : Fin p)=(y : Fin p) ↔ (p:Int) ∣ x-y := by
  rw [IsCharP.intCast_ext_iff (α := Fin p) p,Int.dvd_iff_emod_eq_zero]
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero

theorem red_rep {p} [NeZero p] (x : Fin p) : ((x.val:Int):Fin p)=x := by
  rw [Ring.intCast_natCast]
  exact Fin.ofNat_val_eq_self x

theorem level_res {p} [NeZero p] (a : Tower p) (n : Nat) : (a.level n:Fin p)=a.res := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Eq.trans _ ih
    apply (red_eq _ _).mpr
    obtain ⟨v,h⟩ := a.compat n
    rw [Int.pow_succ] at h
    exact ⟨(p:Int)^n*v,by grobner⟩

theorem equal_res {p} [NeZero p] {a b : Tower p} (h : a.Equal b) : a.res=b.res := by
  apply (red_eq _ _).mpr
  simpa only [Nat.zero_add,Int.pow_one] using h 0

theorem vanishes_res {p} [NeZero p] {a : Tower p} (h : a.Vanishes) : a.res=0 := by
  apply (red_zero _).mpr
  simpa only [Nat.zero_add,Int.pow_one] using h 0

@[simp] theorem res_con {p} [NeZero p] (a : Int) : (con p a).res = (a:Fin p) := rfl
@[simp] theorem res_plus {p} [NeZero p] (a b : Tower p) : (plus a b).res = a.res+b.res := by
  exact Ring.intCast_add _ _
@[simp] theorem res_times {p} [NeZero p] (a b : Tower p) : (times a b).res = a.res*b.res := by
  exact Ring.intCast_mul _ _

theorem vanish_left {p} {a : Tower p} (h : a.Vanishes) (b : Tower p) : (times a b).Vanishes := by
  intro n
  obtain ⟨v,hv⟩ := h n
  exact ⟨v*b.level n,by change _ = _; simp only [times]; grobner⟩

theorem vanish_right {p} (a : Tower p) {b : Tower p} (h : b.Vanishes) : (times a b).Vanishes := by
  intro n
  obtain ⟨v,hv⟩ := h n
  exact ⟨a.level n*v,by simp only [times]; grobner⟩

end Tower
open Tower

/-- One Newton correction, with the exact modulus and the same residue direction. -/
private def Good {p} [NeZero p] (a b : Tower p) (x0 : Fin p) (n : Nat) (x : Int) : Prop :=
  (x:Fin p)=x0 ∧ (p:Int)^(n+1) ∣ a.level n*x^2+b.level n

private theorem next_root {p} [NeZero p] (prime : Prime p) (a b : Tower p) (x0 : Fin p)
    (simple : 2*a.res*x0 ≠ 0) {n x} (good : Good a b x0 n x) :
    ∃ y : Int, Good a b x0 (n+1) y ∧ (p:Int)^(n+1) ∣ y-x := by
  let M := (p:Int)^(n+1)
  obtain ⟨v,hv⟩ := good.2
  obtain ⟨u,hu⟩ := a.compat n
  obtain ⟨w,hw⟩ := b.compat n
  let quot := v+u*x^2+w
  have old : a.level (n+1)*x^2+b.level (n+1)=M*quot := by dsimp [M,quot]; grobner
  obtain ⟨r,hr⟩ := solve_linear prime (2*a.res*x0) (-(quot : Fin p)) simple
  let c : Int := (r.val:Int)
  have rc : (c:Fin p)=r := red_rep r
  have zero : ((quot+2*a.level (n+1)*x*c:Int):Fin p)=0 := by
    simp only [Ring.intCast_add,Ring.intCast_mul,
               level_res a (n+1),good.1,rc]
    grobner
  obtain ⟨l,hl⟩ := (red_zero _).mp zero
  let y := x+M*c
  have keep : M ∣ y-x := ⟨c,by dsimp [y]; grobner⟩
  have small : (p:Int) ∣ y-x := by
    obtain ⟨u,hu⟩ := keep
    dsimp [M] at hu
    rw [Int.pow_succ] at hu
    exact ⟨(p:Int)^n*u,by grobner⟩
  refine ⟨y,⟨((red_eq _ _).mpr small).trans good.1,?_⟩,keep⟩
  refine ⟨l+a.level (n+1)*(p:Int)^n*c^2,?_⟩
  change a.level (n+1)*y^2+b.level (n+1) = (p:Int)^(n+1+1)*_
  rw [Int.pow_succ _ (n+1)]
  dsimp [y,M] at *
  rw [Int.pow_succ _ n] at *
  grobner

private theorem base_root {p} [NeZero p] (a b : Tower p) (x0 : Fin p)
    (root : a.res*x0^2+b.res=0) : Good a b x0 0 (x0.val:Int) := by
  refine ⟨red_rep x0,?_⟩
  change (p:Int)^1 ∣ _
  rw [Int.pow_one]
  apply (red_zero _).mp
  simp only [Ring.intCast_add,Ring.intCast_mul,Ring.intCast_pow,red_rep]
  exact root

private noncomputable def approximations {p} [NeZero p] (prime : Prime p)
    (a b : Tower p) (x0 : Fin p) (root : a.res*x0^2+b.res=0) (simple : 2*a.res*x0 ≠ 0) :
    (n : Nat) → {x : Int // Good a b x0 n x}
  | 0 => ⟨(x0.val:Int),base_root a b x0 root⟩
  | n+1 =>
    let prev := approximations prime a b x0 root simple n
    let step := next_root prime a b x0 simple prev.property
    ⟨Classical.choose step,(Classical.choose_spec step).1⟩

theorem quadratic_hensel {p} [NeZero p] (prime : Prime p) (a b : Tower p) (x0 : Fin p)
    (root : a.res*x0^2+b.res=0) (simple : 2*a.res*x0 ≠ 0) :
    ∃ x : Tower p, x.res=x0 ∧ ∀ n, (p:Int)^(n+1) ∣ a.level n*(x.level n)^2+b.level n := by
  let approx := approximations prime a b x0 root simple
  let x : Tower p := ⟨fun n => (approx n).val, by
    intro n
    exact (Classical.choose_spec (next_root prime a b x0 simple (approx n).property)).2⟩
  exact ⟨x,(approx 0).property.1,fun n => (approx n).property.2⟩


private theorem nonzero_product {p} [NeZero p] (prime : Prime p) {u v : Fin p}
    (hu : u≠0) (hv : v≠0) : u*v≠0 :=
  fun h => (BinaryQuartic.mul_zero prime h).elim hu hv

private theorem nonzero_one_two {p} [NeZero p] (prime : Prime p) (odd : p%2=1) :
    (1:Fin p) ≠ 0 ∧ (2:Fin p) ≠ 0 := by
  have hp := prime.1
  constructor <;> intro h
  · have c := congrArg Fin.val h
    change 1%p=0 at c
    rw [Nat.mod_eq_of_lt (by omega : 1<p)] at c
    contradiction
  · have c := congrArg Fin.val h
    change 2%p=0 at c
    rw [Nat.mod_eq_of_lt (by omega : 2<p)] at c
    contradiction

def Root {p} [NeZero p] (a b c d : Fin p) : Prop :=
  ∃ u v : Fin p, (u≠0 ∨ v≠0) ∧ BinaryQuartic.form a b c d u v=0

/-- At a root in the affine chart, the derivative of the *product* is nonzero. -/
theorem simple_affine_root {p} [NeZero p] (prime : Prime p) (odd : p%2=1)
    (a b c d z : Fin p) (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0)
    (det : a*d-b*c≠0) (root : (a*z^2+b)*(c*z^2+d)=0) :
    2*z*(a*(c*z^2+d)+c*(a*z^2+b))≠0 := by
  have two := (nonzero_one_two prime odd).2
  rcases BinaryQuartic.mul_zero prime root with h|h
  · have zunit : z≠0 := by intro zz; apply hb; grobner
    have other : c*z^2+d≠0 := by intro hh; apply det; grobner
    have unit := nonzero_product prime (nonzero_product prime two zunit)
      (nonzero_product prime ha other)
    intro hz; apply unit; grobner
  · have zunit : z≠0 := by intro zz; apply hd; grobner
    have other : a*z^2+b≠0 := by intro hh; apply det; grobner
    have unit := nonzero_product prime (nonzero_product prime two zunit)
      (nonzero_product prime hc other)
    intro hz; apply unit; grobner

/-- Unit leading coefficients rule out the root at infinity. -/
theorem root_to_affine {p} [NeZero p] (prime : Prime p) (a b c d : Fin p)
    (ha : a≠0) (hc : c≠0) (root : Root a b c d) :
    ∃ z : Fin p, a*z^2+b=0 ∨ c*z^2+d=0 := by
  obtain ⟨u,v,primitive,h⟩ := root
  unfold BinaryQuartic.form at h
  have hv : v≠0 := by
    intro zero
    have hu : u≠0 := primitive.elim id (fun bad => False.elim (bad zero))
    have hsq : u^2≠0 := by
      have square := nonzero_product prime hu hu
      intro h; apply square; grobner
    have left := nonzero_product prime ha hsq
    have right := nonzero_product prime hc hsq
    apply nonzero_product prime left right
    grobner
  obtain ⟨w,hw⟩ := solve_linear prime v 1 hv
  rcases BinaryQuartic.mul_zero prime h with r|r
  · exact ⟨u*w,Or.inl (by grobner)⟩
  · exact ⟨u*w,Or.inr (by grobner)⟩

def Quad {p} (a b u v : Tower p) := plus (times a (sq u)) (times b (sq v))
def Quart {p} (a b c d u v : Tower p) := times (Quad a b u v) (Quad c d u v)
def RHS {p} (k a b c d u v : Tower p) := times k (Quart a b c d u v)

theorem residue_rhs {p} [NeZero p] (k a b c d u v : Tower p) :
    (RHS k a b c d u v).res = k.res*BinaryQuartic.form a.res b.res c.res d.res u.res v.res := by
  simp only [RHS,Quart,Quad,sq,res_times,res_plus,BinaryQuartic.form]
  grobner

/-- Equality after clearing powers of p from two signed-valuation representatives. -/
def Balance {p} (i j : Int) (x y : Tower p) : Prop :=
  (times (con p ((p:Int)^(i-j).toNat)) x).Equal
    (times (con p ((p:Int)^(j-i).toNat)) y)

/-- The left side represents y², either zero or p^(2h) times the square of a unit.
    The right represents p^e times the integral value r. -/
def SquareValue {p} [NeZero p] (e : Int) (r : Tower p) : Prop :=
  r.Vanishes ∨ ∃ h : Int, ∃ y : Tower p, y.res≠0 ∧ Balance (2*h) e (sq y) r

def Soluble {p} [NeZero p] (e : Int) (k a b c d : Tower p) : Prop :=
  ∃ u v : Tower p, (u.res≠0 ∨ v.res≠0) ∧ SquareValue e (RHS k a b c d u v)

def Affine {p} [NeZero p] (e : Int) (k a b c d : Tower p) : Prop :=
  ∃ u : Tower p, SquareValue e (RHS k a b c d u (con p 1))

private theorem imbalance {p} [NeZero p] {i j : Int} {x y : Tower p}
    (hx : x.res≠0) (hy : y.res≠0) (eq : Balance i j x y) : i=j := by
  have r := equal_res eq
  have castp : ((p:Int):Fin p)=0 := (red_zero _).mpr (Int.dvd_refl _)
  have zeroPow : ∀ n : Nat, 0<n → (0:Fin p)^n=0 := by
    intro n h
    cases n with
    | zero => omega
    | succ n => rw [Semiring.pow_succ]; grobner
  simp only [res_times,res_con,Ring.intCast_pow,castp] at r
  by_cases h : i<j
  · have ii : (i-j).toNat=0 := by omega
    rw [ii,Semiring.pow_zero,zeroPow _ (by omega)] at r
    exact False.elim (hx (by grobner))
  · by_cases h' : j<i
    · have jj : (j-i).toNat=0 := by omega
      rw [jj,Semiring.pow_zero,zeroPow _ (by omega)] at r
      exact False.elim (hy (by grobner))
    · omega

private theorem balanced_equal {p} (e : Int) {x y : Tower p} (h : x.Equal y) : Balance e e x y := by
  intro n
  change _ ∣ ((p:Int)^(e-e).toNat)*x.level n-((p:Int)^(e-e).toNat)*y.level n
  simpa using h n

/-- If all primitive right-hand sides have nonzero reduction, a square has even valuation. -/
theorem necessary {p} [NeZero p] (prime : Prime p) (e : Int) (k a b c d : Tower p)
    (hk : k.res≠0) (point : Soluble e k a b c d) :
    (∃ h : Int, e=2*h) ∨ Root a.res b.res c.res d.res := by
  obtain ⟨u,v,primitive,witness⟩ := point
  by_cases root : Root a.res b.res c.res d.res
  · exact Or.inr root
  · left
    have good : (RHS k a b c d u v).res ≠ 0 := by
      rw [residue_rhs]
      exact nonzero_product prime hk (fun hz => root ⟨u.res,v.res,primitive,hz⟩)
    rcases witness with zero | ⟨h,y,unit,eq⟩
    · exact False.elim (good (vanishes_res zero))
    · have unit' : (sq y).res≠0 := by
        simpa only [sq,res_times] using nonzero_product prime unit unit
      exact ⟨h,(imbalance unit' good eq).symm⟩

private theorem factor_lift {p} [NeZero p] (prime : Prime p) (odd : p%2=1)
    (a b : Tower p) (ha : a.res≠0) (hb : b.res≠0) (z : Fin p) (hz : a.res*z^2+b.res=0) :
    ∃ u : Tower p, (Quad a b u (con p 1)).Vanishes := by
  have nz : z≠0 := by intro he; apply hb; grobner
  have simple := nonzero_product prime (nonzero_product prime (nonzero_one_two prime odd).2 ha) nz
  obtain ⟨u,_,roots⟩ := quadratic_hensel prime a b z hz simple
  refine ⟨u,?_⟩
  intro n
  obtain ⟨x,hx⟩ := roots n
  exact ⟨x,by simp only [Quad,plus,times,sq,con]; grobner⟩

theorem affine_of_root {p} [NeZero p] (prime : Prime p) (odd : p%2=1)
    (e : Int) (k a b c d : Tower p) (ha : a.res≠0) (hb : b.res≠0)
    (hc : c.res≠0) (hd : d.res≠0) (root : Root a.res b.res c.res d.res) :
    Affine e k a b c d := by
  obtain ⟨z,hz|hz⟩ := root_to_affine prime _ _ _ _ ha hc root
  · obtain ⟨u,hu⟩ := factor_lift prime odd a b ha hb z hz
    exact ⟨u,Or.inl (vanish_right k (vanish_left hu _))⟩
  · obtain ⟨u,hu⟩ := factor_lift prime odd c d hc hd z hz
    exact ⟨u,Or.inl (vanish_right k (vanish_right _ hu))⟩


/-- Exact lifting of a nonzero square residue at an odd prime. -/
theorem unit_square_lift {p} [NeZero p] (prime : Prime p) (odd : p%2=1)
    (r : Tower p) (z : Fin p) (hz : z≠0) (root : z^2=r.res) :
    ∃ y : Tower p, y.res=z ∧ (sq y).Equal r := by
  have rr : (con p 1).res*z^2+(opposite r).res=0 := by
    have neg : (opposite r).res = -r.res := Ring.intCast_neg _
    rw [neg,res_con,Ring.intCast_one]
    grobner
  have deriv : 2*(con p 1).res*z≠0 := by
    have two := (nonzero_one_two prime odd).2
    have prod := nonzero_product prime two hz
    rw [res_con,Ring.intCast_one]
    intro h; apply prod; grobner
  obtain ⟨y,yr,h⟩ := quadratic_hensel prime (con p 1) (opposite r) z rr deriv
  refine ⟨y,yr,?_⟩
  intro n
  obtain ⟨w,hw⟩ := h n
  simp only [con,opposite] at hw
  exact ⟨w,by simp only [sq,times]; grobner⟩

theorem affine_sufficient {p} [NeZero p] (prime : Prime p) (odd : p%2=1)
    (e : Int) (k a b c d : Tower p) (hk : k.res≠0)
    (ha : a.res≠0) (hb : b.res≠0) (hc : c.res≠0) (hd : d.res≠0)
    (det : a.res*d.res-b.res*c.res≠0)
    (condition : (∃ h : Int, e=2*h) ∨ Root a.res b.res c.res d.res) :
    Affine e k a b c d := by
  rcases condition with ⟨h,eh⟩|root
  · obtain ⟨u,z,hz⟩ := finite_affine prime odd a.res b.res c.res d.res k.res det hk
    let up := con p (u.val:Int)
    let r := RHS k a b c d up (con p 1)
    have unit1 : (1:Fin p)≠0 := (nonzero_one_two prime odd).1
    have ur : up.res = u := red_rep u
    have rr : r.res=k.res*BinaryQuartic.form a.res b.res c.res d.res u 1 := by
      rw [show r.res = _ from residue_rhs k a b c d up (con p 1), ur,res_con,Ring.intCast_one]
    by_cases z0 : z=0
    · have prod0 : k.res*BinaryQuartic.form a.res b.res c.res d.res u 1=0 := by grobner
      have fr := (BinaryQuartic.mul_zero prime prod0).resolve_left hk
      exact affine_of_root prime odd e k a b c d ha hb hc hd ⟨u,1,Or.inr unit1,fr⟩
    · obtain ⟨y,yr,eq⟩ := unit_square_lift prime odd r z z0 (hz.trans rr.symm)
      refine ⟨up,Or.inr ⟨h,y,by rw [yr]; exact z0,?_⟩⟩
      rw [eh]
      exact balanced_equal (2*h) eq
  · exact affine_of_root prime odd e k a b c d ha hb hc hd root

/-- The local binary-quartic criterion over the inverse-limit presentation of p-adic integers.
    The multiplier is a p-adic unit k times p to the arbitrary signed exponent e. -/
theorem soluble_iff {p} [NeZero p] (prime : Prime p) (odd : p%2=1)
    (e : Int) (k a b c d : Tower p) (hk : k.res≠0)
    (ha : a.res≠0) (hb : b.res≠0) (hc : c.res≠0) (hd : d.res≠0)
    (det : a.res*d.res-b.res*c.res≠0) :
    Soluble e k a b c d ↔ (∃ h : Int, e=2*h) ∨ Root a.res b.res c.res d.res := by
  constructor
  · exact necessary prime e k a b c d hk
  · intro cond
    obtain ⟨u,h⟩ := affine_sufficient prime odd e k a b c d hk ha hb hc hd det cond
    have one : (con p 1).res≠0 := by
      rw [res_con,Ring.intCast_one]; exact (nonzero_one_two prime odd).1
    exact ⟨u,con p 1,Or.inr one,h⟩

/-- Every soluble fibre already has a point with the second projective coordinate equal to one. -/
theorem affine_iff {p} [NeZero p] (prime : Prime p) (odd : p%2=1)
    (e : Int) (k a b c d : Tower p) (hk : k.res≠0)
    (ha : a.res≠0) (hb : b.res≠0) (hc : c.res≠0) (hd : d.res≠0)
    (det : a.res*d.res-b.res*c.res≠0) :
    Affine e k a b c d ↔ Soluble e k a b c d := by
  constructor
  · rintro ⟨u,h⟩
    have one : (con p 1).res≠0 := by
      rw [res_con,Ring.intCast_one]; exact (nonzero_one_two prime odd).1
    exact ⟨u,con p 1,Or.inr one,h⟩
  · intro point
    exact affine_sufficient prime odd e k a b c d hk ha hb hc hd det (necessary prime e k a b c d hk point)

end AdicQuartic

#print axioms AdicQuartic.quadratic_hensel
#print axioms AdicQuartic.simple_affine_root
#print axioms AdicQuartic.root_to_affine
#print axioms AdicQuartic.unit_square_lift
#print axioms AdicQuartic.affine_of_root
#print axioms AdicQuartic.necessary
#print axioms AdicQuartic.soluble_iff
#print axioms AdicQuartic.affine_iff
