import TraceExpressions

namespace Sun28.TraceAtlas
open ZInQ GroupCharts GroupCharts.PointCode Forward Ordinary ScalarHeight WitnessIndices
noncomputable section
variable {R : Type*} [CommRing R]
abbrev PE (R : Type*) := Program R (PointCode R)
abbrev PointValue (φ : R →+* ℚ) (p : PE R) (P : CPoint) := GroupCharts.Represents φ (Program.eval φ p) P

def ordered (w : NinePoints) : Fin 9 → CPoint :=
  ![w.Q,w.N,w.T,w.Z,w.H,w.U 0,w.U 1,w.U 2,w.U 3]

structure Codes (R : Type*) where
  q : PointCode R
  n : PointCode R
  t : PointCode R
  z : PointCode R
  h : PointCode R
  u : Fin 4 → PointCode R

structure Inputs (φ : R →+* ℚ) (p : Codes R) (w : NinePoints) : Prop where
  q : GroupCharts.Represents φ p.q w.Q
  n : GroupCharts.Represents φ p.n w.N
  t : GroupCharts.Represents φ p.t w.T
  z : GroupCharts.Represents φ p.z w.Z
  h : GroupCharts.Represents φ p.h w.H
  u : ∀ i, GroupCharts.Represents φ (p.u i) (w.U i)

def fromNine (p : Fin 9 → PointCode R) : Codes R :=
  ⟨p 0,p 1,p 2,p 3,p 4,fun i => p ⟨i.val+5,by omega⟩⟩

theorem inputs_of_nine (φ : R →+* ℚ) (p : Fin 9 → PointCode R) (w : NinePoints)
    (h : ∀ i, GroupCharts.Represents φ (p i) (ordered w i)) : Inputs φ (fromNine p) w := by
  refine ⟨h 0,h 1,h 2,h 3,h 4,?_⟩
  intro i
  fin_cases i <;> first | exact h 5 | exact h 6 | exact h 7 | exact h 8

def abscissa : PointCode R → Quad R
  | .infinity => Quad.zero
  | .affine x _ => x

theorem abscissa_spec (φ : R →+* ℚ) {x : PointCode R} {P : CPoint}
    (h : GroupCharts.Represents φ x P) : Quad.Value φ (abscissa x) (curveX P) := by
  cases h with
  | infinity => exact Quad.zero_value φ
  | affine _ hx _ => exact hx

def pointX (q : PE R) : E R := Program.bind (fun p => .pure (abscissa p)) q
def recip (q : PE R) : E R := Program.bind PointCode.reciprocal q
def param (q : PE R) : E R := Program.bind PointCode.parameter q

theorem pointX_spec (φ : R →+* ℚ) {q : PE R} {Q : CPoint} (h : PointValue φ q Q) :
    Denotes φ (pointX q) (curveX Q) := by
  simpa only [Denotes,pointX,Program.eval_bind,Program.eval] using abscissa_spec φ h
theorem recip_spec (φ : R →+* ℚ) {q : PE R} {Q : CPoint} (h : PointValue φ q Q) :
    Denotes φ (recip q) (Scalar.reciprocal (scalarEquiv Q)) := by
  simpa only [Denotes,recip,Program.eval_bind] using (readouts_correct φ h).1
theorem param_spec (φ : R →+* ℚ) {q : PE R} {Q : CPoint} (h : PointValue φ q Q) :
    Denotes φ (param q) (Scalar.parameter (scalarEquiv Q)) := by
  simpa only [Denotes,param,Program.eval_bind] using (readouts_correct φ h).2

def rsc (p : Codes R) (M : ℕ) : PE R := mulProgram M p.q
def roots (p : Codes R) (M : ℕ) : Fin 4 → PE R :=
  ![.pure p.n, Program.bind (addProgram generator) (rsc p M),.pure p.t,.pure p.z]
def base (p : Codes R) (c : ℤ) : PE R := translate c p.h generator
def shifted (p : Codes R) (M : ℕ) (c : ℤ) (i : Fin 4) : PE R :=
  Program.bind (fun q => translate c (p.u i) q) (roots p M i)

namespace Inputs
variable {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (hp : Inputs φ p w)
include hp
theorem rsc (M : ℕ) : PointValue φ (rsc p M) (WitnessIndices.scalarPoint w M) :=
  mul_correct φ M hp.q
theorem roots (M : ℕ) (i : Fin 4) : PointValue φ (roots p M i) (rootPoints w M i) := by
  fin_cases i
  · exact hp.n
  · change GroupCharts.Represents φ (Program.eval _ (Program.bind _ _)) _
    rw [Program.eval_bind]
    exact add_correct φ (generator_correct φ) (hp.rsc M)
  · exact hp.t
  · exact hp.z
theorem base (c : ℤ) : PointValue φ (base p c) (translatedBase w c) :=
  translate_correct φ c hp.h (generator_correct φ)
theorem shifted (M : ℕ) (c : ℤ) (i : Fin 4) : PointValue φ (shifted p M c i) (translated w M c i) := by
  change GroupCharts.Represents φ (Program.eval _ (Program.bind _ _)) _
  rw [Program.eval_bind]
  exact translate_correct φ c (hp.u i) (hp.roots M i)

end Inputs

def sumN (f : ℕ → E R) : ℕ → E R
  | 0 => lit 0
  | k+1 => add (sumN f k) (f k)

theorem sumN_spec (φ : R →+* ℚ) (f : ℕ → E R) (g : ℕ → K0)
    (h : ∀ i, Denotes φ (f i) (g i)) (k : ℕ) :
    Denotes φ (sumN f k) (∑ i ∈ Finset.range k, g i) := by
  induction k with
  | zero => simpa [sumN] using lit_spec φ (0:K0)
  | succ k ih => simpa only [sumN,Finset.sum_range_succ] using Denotes.add ih (h k)

def trunc (q : PE R) : E R :=
  let coeff := shortDifferential (-(3-sqrt2)^2:K0)
  sumN (fun i => mul (lit (coeff (i+1)/(i+1:ℕ))) (power (param q) (i+1))) 64

theorem trunc_spec (φ : R →+* ℚ) {q : PE R} {Q : CPoint} (h : PointValue φ q Q) :
    Denotes φ (trunc q) (truncAt Q) := by
  unfold trunc truncAt logTrunc
  apply sumN_spec
  intro i
  rw [mul_div_right_comm]
  exact Denotes.mul (lit_spec _ _) (Denotes.power (param_spec φ h) _)

def ratio (p q : PE R) := div (trunc p) (trunc q)

theorem ratio_spec (φ : R →+* ℚ) {p q : PE R} {P Q : CPoint}
    (h : PointValue φ p P) (k : PointValue φ q Q) :
    Denotes φ (ratio p q) (pointRatio P Q) :=
  Denotes.div (trunc_spec φ h) (trunc_spec φ k)

def deltaTest (s t z : E R) : E R :=
  let sm := sub s (lit 2)
  sub (add (sub (power t 2) (mul (mul (mul s sm) t) z)) (mul (power sm 2) (power z 2))) (lit 1)

theorem delta_spec {φ : R →+* ℚ} {s t z : E R} {S T Z : K0}
    (hs : Denotes φ s S) (ht : Denotes φ t T) (hz : Denotes φ z Z) :
    Denotes φ (deltaTest s t z) (lucas S T Z) := by
  unfold deltaTest lucas
  have hm := Denotes.sub hs (lit_spec φ 2)
  exact Denotes.sub (Denotes.add (Denotes.sub (Denotes.power ht 2) (Denotes.mul (Denotes.mul
    (Denotes.mul hs hm) ht) hz)) (Denotes.mul (Denotes.power hm 2) (Denotes.power hz 2))) (lit_spec φ 1)

def ordinary (p : Codes R) (M : ℕ) (c : ℤ) (b : E R) : OrdinaryTest → E R :=
  let L := fun i => ratio (.pure (p.u i)) (.pure p.h)
  let V := shifted p M c
  let V₀ := base p c
  fun i => match i with
    | .h => recip (.pure p.h)
    | .u j => recip (.pure (p.u j))
    | .v₀ => conj (recip V₀)
    | .v j => conj (recip (V j))
    | .difference j => sub (L j) (conj (ratio (V j) V₀))
    | .delta => deltaTest (L 1) (L 2) (L 3)
    | .beta => sub (L 0) b

theorem ordinary_spec {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (h : Inputs φ p w)
    (M : ℕ) (c : ℤ) {b : E R} {β : ℚ} (hb : RatValue φ b β) (i : OrdinaryTest) :
    Denotes φ (ordinary p M c b i) (ordinaryAt w M c β i) := by
  have hr (j : Fin 4) := ratio_spec φ (q:=.pure p.h) (p:=.pure (p.u j)) (h.u j) h.h
  cases i with
  | h => exact recip_spec φ (q:=.pure p.h) h.h
  | u j => exact recip_spec φ (q:=.pure (p.u j)) (h.u j)
  | v₀ => exact Denotes.conj (recip_spec φ (h.base c))
  | v j => exact Denotes.conj (recip_spec φ (h.shifted M c j))
  | difference j => exact Denotes.sub (hr j) (Denotes.conj (ratio_spec φ (h.shifted M c j) (h.base c)))
  | delta => exact delta_spec (hr 1) (hr 2) (hr 3)
  | beta => exact Denotes.sub (hr 0) hb

def rootProd (p : Codes R) (M : ℕ) : E R := prodSet Finset.univ (fun i => pointX (roots p M i))

theorem prod_correct {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (h : Inputs φ p w) (M : ℕ) :
    Denotes φ (rootProd p M) (rootProduct w M) := prod_spec φ _ _ _ (fun i => pointX_spec φ (h.roots M i))

def scales (p : Codes R) (M : ℕ) : Fin 3 → E R :=
  let t := rootProd p M
  ![lit 1,realPart t,add (lit 1) (power (imagPart t) 2)]

theorem scales_correct {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (h : Inputs φ p w)
    (M : ℕ) (j : Fin 3) : RatValue φ (scales p M j) (pointScale w M j) := by
  have e := prod_correct h M
  fin_cases j
  · simpa [RatValue,pointScale,scaleRoot,scales] using lit_spec φ (1:K0)
  · exact Denotes.realPart e
  · change Denotes _ _ (algebraMap ℚ K0 (1+(rootProduct w M).im^2))
    rw [map_add,map_one,map_pow]
    exact Denotes.add (lit_spec φ 1) (Denotes.power (Denotes.imagPart e) 2)

end
#print axioms inputs_of_nine
#print axioms trunc_spec
#print axioms ordinary_spec
#print axioms scales_correct
end Sun28.TraceAtlas
