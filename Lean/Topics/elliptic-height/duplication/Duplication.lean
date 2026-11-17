import Std

namespace EllipticHeight.Duplication
open Lean.Grind Std

def first {K : Type} [CommRing K] (D a b : K) := (a^2+D*b^2)^2
def second {K : Type} [CommRing K] (D a b : K) := 4*a*b*(a^2-D*b^2)

private theorem nonzero_mul {K : Type} [Field K] {x y : K} (hx : x≠0) (hy : y≠0) :
    x*y≠0 := fun h => (Field.of_mul_eq_zero h).elim hx hy

/-- The two homogeneous forms have no common projective zero at a good prime. -/
theorem good_reduction {K : Type} [Field K] (D a b : K)
    (two : (2:K)≠0) (unit : D≠0) (primitive : a≠0 ∨ b≠0) :
    first D a b≠0 ∨ second D a b≠0 := by
  by_cases hf : first D a b=0
  · apply Or.inr
    intro hg
    have f : (a^2+D*b^2)*(a^2+D*b^2)=0 := by
      simpa only [first,Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul] using hf
    have plus := (Field.of_mul_eq_zero f).elim id id
    have b0 : b≠0 := by
      intro z
      have aa : a*a=0 := by
        simpa only [z,Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul,Semiring.mul_zero,
          Semiring.add_zero] using plus
      exact primitive.elim (fun h=>((Field.of_mul_eq_zero aa).elim h h)) (fun h=>h z)
    have a0 : a≠0 := by
      intro z
      have e : (0:K)+D*(b*b)=0 := by
        simpa only [z,Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul,Semiring.mul_zero] using plus
      have h : D*(b*b)=0 := by grind
      exact nonzero_mul unit (nonzero_mul b0 b0) h
    have four : (4:K)≠0 := by
      have h : (4:K)=2*2 := by grobner
      rw [h]; exact nonzero_mul two two
    have sub := (Field.of_mul_eq_zero hg).resolve_left (nonzero_mul (nonzero_mul four a0) b0)
    have vanished : (2:K)*(a*a)=0 := by grind
    exact nonzero_mul two (nonzero_mul a0 a0) vanished
  · exact Or.inl hf

/-- The real-place doubling error on the positive double branch. -/
theorem arch_double {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K]
    [IsLinearOrder K] [OrderedRing K] (u : K) (lo : 0≤u) (hi : u≤1) :
    1≤(1+u)^2 ∧ (1+u)^2≤4 := by
  have a:=OrderedRing.mul_nonneg lo (show (0:K)≤2+u by grind)
  have b:=OrderedRing.mul_nonneg (show (0:K)≤1-u by grind) (show (0:K)≤3+u by grind)
  grind

/-- Integral coordinates in the basis (1,√2), with concrete reduction maps. -/
structure Quad where
  a : Int
  b : Int
deriving DecidableEq, Repr

namespace Quad
def add (x y : Quad) : Quad := ⟨x.a+y.a,x.b+y.b⟩
def sub (x y : Quad) : Quad := ⟨x.a-y.a,x.b-y.b⟩
def mul (x y : Quad) : Quad := ⟨x.a*y.a+2*x.b*y.b,x.a*y.b+x.b*y.a⟩
def sq (x : Quad) := x.mul x
def norm (x : Quad) := x.a^2-2*x.b^2
def eval (r : Int) (x : Quad) := x.a+r*x.b
end Quad

def D : Quad := ⟨11,-6⟩
def firstK (a b : Quad) := (a.sq.add (D.mul b.sq)).sq
def secondK (a b : Quad) := (((⟨4,0⟩ : Quad).mul a).mul b).mul (a.sq.sub (D.mul b.sq))

private theorem eval_mul (r : Int) (x y : Quad) :
    Quad.eval r (x.mul y)=Quad.eval r x*Quad.eval r y+(2-r^2)*x.b*y.b := by
  unfold Quad.eval Quad.mul; grobner

private theorem eval_add (r : Int) (x y : Quad) :
    Quad.eval r (x.add y)=Quad.eval r x+Quad.eval r y := by
  unfold Quad.eval Quad.add; grobner

private theorem modular_add (p r : Int) (x y : Quad) :
    Quad.eval r (x.add y)%p=(Quad.eval r x%p+Quad.eval r y%p)%p := by
  rw [eval_add,Int.add_emod]

private theorem modular_mul (p r : Int) (root : (2-r^2)%p=0) (x y : Quad) :
    Quad.eval r (x.mul y)%p=(Quad.eval r x%p)*(Quad.eval r y%p)%p := by
  rw [eval_mul,Int.add_emod,Int.mul_emod ((2-r^2)*x.b),Int.mul_emod (2-r^2),root]
  simp [Int.mul_emod]

private theorem mod_sq (p r : Int) (root : (2-r^2)%p=0) (x : Quad) :
    Quad.eval r x.sq%p=(Quad.eval r x%p)*(Quad.eval r x%p)%p :=
  modular_mul p r root x x

def regularPair (a b : Quad) := Quad.eval 0 a%2=1 ∧ Quad.eval 0 b%2=0 ∧ Quad.eval 3 a%7=1

/-- Above 2 the denominator stays divisible and numerator a unit. Above 7 the
numerator remains 1 modulo (3−√2), for any denominator. -/
theorem regular_step (a b : Quad) (s : regularPair a b) :
    regularPair (firstK a b) (secondK a b) := by
  obtain ⟨a2,b2,a7⟩:=s
  have root2 : (2-(0:Int)^2)%2=0 := by decide
  have root7 : (2-(3:Int)^2)%7=0 := by decide
  have d7 : Quad.eval 3 D%7=0 := by decide
  have four2 : Quad.eval 0 (⟨4,0⟩:Quad)%2=0 := by decide
  refine ⟨?_,?_,?_⟩
  · unfold firstK
    simp only [mod_sq 2 0 root2,modular_add,modular_mul 2 0 root2,a2,b2,Int.mul_zero,
      Int.zero_emod,Int.add_zero]
    decide
  · unfold secondK
    simp only [modular_mul 2 0 root2,four2,Int.zero_mul,Int.zero_emod]
  · unfold firstK
    simp only [mod_sq 7 3 root7,modular_add,modular_mul 7 3 root7,d7,a7,
      Int.zero_mul,Int.zero_emod,Int.add_zero]
    decide

def orbit : Nat → Quad × Quad
  | 0 => (⟨57,-28⟩,⟨8,0⟩)
  | n+1 => let p:=orbit n; (firstK p.1 p.2,secondK p.1 p.2)

theorem regular_orbit (n : Nat) : regularPair (orbit n).1 (orbit n).2 := by
  induction n with
  | zero => unfold regularPair; decide
  | succ n ih => exact regular_step _ _ ih

theorem exact_norms :
    Quad.norm (orbit 0).1=41^2 ∧ Quad.norm (orbit 1).1=4905889^2 ∧
    (4:Nat)*41^12<4905889^3 ∧ Quad.norm (⟨12,-6⟩:Quad)=72 := by decide

attribute [local instance] Semiring.natCast Ring.intCast
variable {K : Type} [Field K]

def realize (s : K) (x : Quad) : K := (x.a:K)+(x.b:K)*s

private theorem realize_add (s : K) (x y : Quad) :
    realize s (x.add y)=realize s x+realize s y := by
  simp only [realize,Quad.add,Ring.intCast_add]; grobner

private theorem realize_sub (s : K) (x y : Quad) :
    realize s (x.sub y)=realize s x-realize s y := by
  simp only [realize,Quad.sub,Ring.intCast_sub]; grobner

private theorem realize_mul (s : K) (root : s^2=2) (x y : Quad) :
    realize s (x.mul y)=realize s x*realize s y := by
  simp only [realize,Quad.mul,Ring.intCast_add,Ring.intCast_mul]
  have two : ((2:Int):K)=2 := by grind
  rw [two,←root]; grobner

private theorem realize_sq (s : K) (root : s^2=2) (x : Quad) :
    realize s x.sq=(realize s x)^2 := by
  rw [Quad.sq,realize_mul s root]; grobner

private theorem coeff (s : K) (root : s^2=2) : realize s D=(3-s)^2 := by
  simp only [realize,D]
  grind

private theorem next_values (s : K) (root : s^2=2) (n : Nat) :
    realize s (orbit (n+1)).1=first ((3-s)^2) (realize s (orbit n).1) (realize s (orbit n).2) ∧
    realize s (orbit (n+1)).2=second ((3-s)^2) (realize s (orbit n).1) (realize s (orbit n).2) := by
  have four : realize s ⟨4,0⟩=4 := by simp only [realize]; grind
  simp only [orbit,firstK,secondK,realize_sq s root,realize_add,realize_mul s root,
    realize_sub,coeff s root,four,first,second,and_self]

private theorem start_values (s : K) :
    realize s (orbit 0).1=57-28*s ∧ realize s (orbit 0).2=8 := by
  simp only [orbit,realize]; grind

/-- Every stored homogeneous iterate is primitive under *every* specialization
of Z[√2] to a field. Applying this to each residue field gives ideal (1). -/
theorem primitive_in_every_residue_field (s : K) (root : s^2=2) (n : Nat) :
    realize s (orbit n).1≠0 ∨ realize s (orbit n).2≠0 := by
  have init:=start_values s
  by_cases dy : (2:K)=0
  · have square : s*s=0 := by grind
    have zero : s=0 := (Field.of_mul_eq_zero square).elim id id
    have state (m : Nat) : realize s (orbit m).1=1 ∧ realize s (orbit m).2=0 := by
      induction m with
      | zero => grind
      | succ m ih =>
        obtain ⟨f,g⟩:=next_values s root m
        unfold first at f; unfold second at g; grind
    exact Or.inl (by grind [state n])
  · by_cases bad : (3-s)^2=0
    · have sq : (3-s)*(3-s)=0 := by grind
      have sub := (Field.of_mul_eq_zero sq).elim id id
      have char7 : (7:K)=0 := by grind
      have state (m : Nat) : realize s (orbit m).1=1 := by
        induction m with
        | zero => grind
        | succ m ih =>
          have h:=(next_values s root m).1
          unfold first at h; grind
      exact Or.inl (by grind [state n])
    · induction n with
      | zero =>
        have x8 : (8:K)≠0 := by
          have e : (8:K)=2*2*2 := by grobner
          rw [e]; exact nonzero_mul (nonzero_mul dy dy) dy
        exact Or.inr (by grind)
      | succ n ih =>
        obtain ⟨f,g⟩:=next_values s root n
        rw [f,g]
        exact good_reduction _ _ _ dy bad ih

theorem dyadic_norm_even (i j : Int) :
    ∃k:Int, Quad.norm (((⟨2*i+1,2*j⟩:Quad).sq).add ⟨1,0⟩)=16*k+4 := by
  let t:=i*i+i+2*j*j
  let u:=(2*i+1)*j
  refine ⟨t*t+t-2*u*u,?_⟩
  unfold Quad.norm Quad.add Quad.sq Quad.mul t u; grobner

theorem dyadic_norm_odd (i j : Int) :
    ∃k:Int, Quad.norm (((⟨2*i+1,2*j+1⟩:Quad).sq).add ⟨1,0⟩)=16*k+8 := by
  let t:=i*i+i+2*j*j+2*j+1
  let u:=i*(2*j+1)+j
  refine ⟨t*t-2*u*u-2*u-1,?_⟩
  unfold Quad.norm Quad.add Quad.sq Quad.mul t u; grobner

theorem seven_nonsquare : ∀ x : Fin 7, (x.val^2+1)%7≠0 := by decide

#print axioms good_reduction
#print axioms arch_double
#print axioms regular_step
#print axioms regular_orbit
#print axioms exact_norms
#print axioms primitive_in_every_residue_field
#print axioms dyadic_norm_even
#print axioms dyadic_norm_odd
#print axioms seven_nonsquare
end EllipticHeight.Duplication
