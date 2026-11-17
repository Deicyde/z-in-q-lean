import Std

namespace IndependentIndices.ChartJets
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

abbrev Poly := List Int

def add : Poly → Poly → Poly
  | [], q => q
  | a::p, [] => a::p
  | a::p, b::q => (a+b)::add p q

def neg (p : Poly) := p.map Int.neg

def mul : Poly → Poly → Poly
  | [], _ => []
  | a::p, q => add (q.map (fun b => a*b)) (0::mul p q)

def power (p : Poly) : Nat → Poly
  | 0 => [1]
  | n+1 => mul (power p n) p

def val {R : Type} [CommRing R] (x : R) : Poly → R
  | [] => 0
  | a::p => (a:R)+x*val x p

private theorem add_val {R : Type} [CommRing R] (x : R) (a b : Poly) :
    val x (add a b)=val x a+val x b := by
  induction a generalizing b with
  | nil => simp only [add,val]; grobner
  | cons c a ih =>
    cases b with
    | nil => simp only [add,val]; grobner
    | cons d b => simp only [add,val,ih,Ring.intCast_add]; grobner

private theorem scale_val {R : Type} [CommRing R] (x : R) (c : Int) (p : Poly) :
    val x (p.map (fun a => c*a))=(c:R)*val x p := by
  induction p with
  | nil => simp only [List.map_nil,val]; grobner
  | cons a p ih => simp only [List.map_cons,val,ih,Ring.intCast_mul]; grobner

theorem mul_val {R : Type} [CommRing R] (x : R) (a b : Poly) :
    val x (mul a b)=val x a*val x b := by
  induction a with
  | nil => simp only [mul,val]; grobner
  | cons c a ih => simp only [mul,add_val,scale_val,val,ih]; grobner

/-- n,d are the numerator and denominator of w(2P). -/
def n : Poly := [0,16,-32,16]
def d : Poly := [1,4,6,4,1]
def s : Poly := [1,-6,1]

def hom (m : Nat) (a : Poly) (i : Nat := 0) : Poly :=
  match a with
  | [] => []
  | c::p => add (mul [c] (mul (power n i) (power d (m-i)))) (hom m p (i+1))

def defect (m : Nat) (a q : Poly) : Poly :=
  add (mul [1,0,-1] (mul (hom m a) q)) (neg (mul s (mul (hom m q) a)))

def short : Poly := [15,-6,-2]
def pNumer : Poly := [515764275,-939815760,471221725,-37862400,-4176000,-742400,-122496,0,12160]
def pDenom : Poly := [515764275,-733510050,246586275]
def mixed : Poly := add (mul pNumer [15]) (neg (mul short pDenom))

/-- The first coefficient after each zero prefix is nonzero. -/
def exactPrefix (p : Poly) (k : Nat) (lc : Int) : Prop :=
  p.take (k+1)=List.replicate k 0 ++ [lc]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem chart_orders :
    exactPrefix (defect 0 [1] [1]) 1 6 ∧
    exactPrefix (defect 2 short [15]) 3 66150 ∧
    exactPrefix (defect 8 pNumer pDenom) 10 8468606090943372488400000 ∧
    exactPrefix mixed 3 (-555438450) := by
  unfold exactPrefix; decide

private theorem zero_prefix_val {R : Type} [CommRing R] {p : Poly} {c : Int} (x : R) (k : Nat)
    (h : exactPrefix p k c) : val x p = x^k * val x (p.drop k) := by
  induction k generalizing p with
  | zero => simp only [List.drop_zero,Semiring.pow_zero]; grobner
  | succ k ih =>
    cases p with
    | nil =>
      simp [exactPrefix,List.replicate_succ] at h
    | cons a p =>
      have head : a=0 ∧ exactPrefix p k c := by
        simpa [exactPrefix,List.replicate_succ] using h
      rw [val,head.1,ih head.2]
      simp only [List.drop_succ_cons, Semiring.pow_succ]; grobner

theorem substitution_orders {R : Type} [CommRing R] (x : R) :
    val x (defect 0 [1] [1])=x*val x ((defect 0 [1] [1]).drop 1) ∧
    val x (defect 2 short [15])=x^3*val x ((defect 2 short [15]).drop 3) ∧
    val x (defect 8 pNumer pDenom)=x^10*val x ((defect 8 pNumer pDenom).drop 10) ∧
    val x mixed=x^3*val x (mixed.drop 3) := by
  exact ⟨by simpa only [Semiring.pow_one] using zero_prefix_val x 1 chart_orders.1,
    zero_prefix_val x 3 chart_orders.2.1, zero_prefix_val x 10 chart_orders.2.2.1,
    zero_prefix_val x 3 chart_orders.2.2.2⟩

#print axioms chart_orders
#print axioms substitution_orders
end IndependentIndices.ChartJets
