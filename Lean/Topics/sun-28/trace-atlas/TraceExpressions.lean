import GroupReadouts
import PoleParameters

/-! Programs of rational expressions from polynomial coordinates in ℚ(√2). -/
namespace Sun28.TraceAtlas
open ZInQ GroupCharts
noncomputable section

variable {R : Type*} [CommRing R]
abbrev E (R : Type*) := Program R (Quad R)
abbrev Denotes (φ : R →+* ℚ) (x : E R) (X : K0) := Quad.Value φ (Program.eval φ x) X
abbrev RatValue (φ : R →+* ℚ) (x : E R) (q : ℚ) := Denotes φ x (algebraMap ℚ K0 q)

def lit (a : K0) : E R :=
  .pure ⟨(a.re.num:R)*(a.im.den:R),(a.im.num:R)*(a.re.den:R),(a.re.den:R)*(a.im.den:R)⟩

theorem lit_spec (φ : R →+* ℚ) (a : K0) : Denotes φ (lit a) a := by
  have nr := Rat.den_ne_zero a.re
  have ni := Rat.den_ne_zero a.im
  have dr : (a.re.den:ℚ)≠0 := by exact_mod_cast nr
  have di : (a.im.den:ℚ)≠0 := by exact_mod_cast ni
  refine ⟨?_,?_⟩
  · simp [lit,Program.eval,Quad.Good,dr,di]
  · ext
    · change φ ((a.re.num:R)*(a.im.den:R)) / φ ((a.re.den:R)*(a.im.den:R)) = a.re
      simp only [map_mul,map_intCast,map_natCast]
      calc _ = (a.re.num:ℚ)/a.re.den := by field_simp
           _ = a.re := Rat.num_div_den _
    · change φ ((a.im.num:R)*(a.re.den:R)) / φ ((a.re.den:R)*(a.im.den:R)) = a.im
      simp only [map_mul,map_intCast,map_natCast]
      calc _ = (a.im.num:ℚ)/a.im.den := by field_simp
           _ = a.im := Rat.num_div_den _

def rat (q : ℚ) : E R := lit (algebraMap ℚ K0 q)

def unary (f : Quad R → Quad R) (a : E R) : E R := Program.bind (fun x => .pure (f x)) a
def binary (f : Quad R → Quad R → Quad R) (a b : E R) : E R :=
  Program.bind (fun x => unary (f x) b) a
def add := @binary R Quad.add
def sub := @binary R Quad.sub
def mul := @binary R Quad.mul
def conj := @unary R Quad.conj
def div (a b : E R) : E R := Program.bind (fun x => Program.bind (fun y => x.totalDiv y) b) a
def realPart := @unary R (fun q => ⟨q.re,0,q.den⟩)
def imagPart := @unary R (fun q => ⟨q.im,0,q.den⟩)

def power (a : E R) : ℕ → E R
  | 0 => lit 1
  | n+1 => mul (power a n) a

namespace Denotes
variable {φ : R →+* ℚ} {a b : E R} {x y : K0}
theorem add (h : Denotes φ a x) (k : Denotes φ b y) : Denotes φ (add a b) (x+y) := by
  simpa only [Denotes,TraceAtlas.add,binary,unary,Program.eval_bind,Program.eval] using Quad.Value.add h k
theorem sub (h : Denotes φ a x) (k : Denotes φ b y) : Denotes φ (sub a b) (x-y) := by
  simpa only [Denotes,TraceAtlas.sub,binary,unary,Program.eval_bind,Program.eval] using Quad.Value.sub h k
theorem mul (h : Denotes φ a x) (k : Denotes φ b y) : Denotes φ (mul a b) (x*y) := by
  simpa only [Denotes,TraceAtlas.mul,binary,unary,Program.eval_bind,Program.eval] using Quad.Value.mul h k
theorem div (h : Denotes φ a x) (k : Denotes φ b y) : Denotes φ (div a b) (x/y) := by
  simpa only [Denotes,TraceAtlas.div,Program.eval_bind] using Quad.totalDiv_value φ h k
theorem conj (h : Denotes φ a x) : Denotes φ (conj a) (Forward.conjugation x) := by
  change Quad.Value φ _ (star x)
  simp only [TraceAtlas.conj,unary,Program.eval_bind,Program.eval]
  exact ⟨h.good,by rw [Quad.eval_conj,h.value]⟩
theorem realPart (h : Denotes φ a x) : RatValue φ (realPart a) x.re := by
  change Quad.Value φ _ _
  simp only [TraceAtlas.realPart,unary,Program.eval_bind,Program.eval]
  refine ⟨h.good,?_⟩
  have e := congrArg QuadraticAlgebra.re h.value
  apply QuadraticAlgebra.ext
  · exact e
  · change φ 0 / φ (Program.eval φ a).den=0
    simp
theorem imagPart (h : Denotes φ a x) : RatValue φ (imagPart a) x.im := by
  change Quad.Value φ _ _
  simp only [TraceAtlas.imagPart,unary,Program.eval_bind,Program.eval]
  refine ⟨h.good,?_⟩
  have e := congrArg QuadraticAlgebra.im h.value
  apply QuadraticAlgebra.ext
  · exact e
  · change φ 0 / φ (Program.eval φ a).den=0
    simp
theorem power (h : Denotes φ a x) (k : ℕ) : Denotes φ (power a k) (x^k) := by
  induction k with
  | zero => simpa [TraceAtlas.power] using lit_spec φ (1:K0)
  | succ n ih => simpa only [TraceAtlas.power,pow_succ] using Denotes.mul ih h

end Denotes

def prodList {I : Type*} (f : I → E R) : List I → E R
  | [] => lit 1
  | i :: l => mul (f i) (prodList f l)

theorem prodList_spec {I : Type*} (φ : R →+* ℚ) (f : I → E R) (g : I → K0)
    (h : ∀ i, Denotes φ (f i) (g i)) (l : List I) :
    Denotes φ (prodList f l) ((l.map g).prod) := by
  induction l with
  | nil => exact lit_spec φ 1
  | cons i l ih => exact Denotes.mul (h i) ih

def prodSet {I : Type*} (s : Finset I) (f : I → E R) : E R := prodList f s.toList

theorem prod_spec {I : Type*} (φ : R →+* ℚ) (s : Finset I) (f : I → E R) (g : I → K0)
    (h : ∀ i, Denotes φ (f i) (g i)) : Denotes φ (prodSet s f) (∏ i ∈ s,g i) := by
  rw [← Finset.prod_map_toList]
  exact prodList_spec φ f g h s.toList

/-- After specializing a rational-valued program, its real numerator and common denominator
are a rational fraction, even on branches where a totalized inner inverse is zero. -/
theorem fraction_value (φ : R →+* ℚ) {a : E R} {x : ℚ} (h : RatValue φ a x) :
    let v := Program.eval φ a
    φ v.den≠0 ∧ φ v.re/φ v.den=x := by
  exact ⟨h.good,congrArg QuadraticAlgebra.re h.value⟩

end
#print axioms lit_spec
#print axioms Denotes.div
#print axioms prod_spec
#print axioms fraction_value
end Sun28.TraceAtlas
