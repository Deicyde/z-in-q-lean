import TracePoints

namespace Sun28.TraceAtlas
open ZInQ GroupCharts Forward Ordinary ScalarHeight WitnessIndices
noncomputable section
variable {R : Type*} [CommRing R]

namespace RatValue
variable {φ : R →+* ℚ} {a b : E R} {x y : ℚ}
theorem rat (φ : R →+* ℚ) (x : ℚ) : RatValue φ (TraceAtlas.rat x) x := lit_spec φ _
theorem add (h : RatValue φ a x) (k : RatValue φ b y) : RatValue φ (add a b) (x+y) := by
  change Denotes _ _ (algebraMap ℚ K0 (x+y)); rw [map_add]; exact Denotes.add h k
theorem sub (h : RatValue φ a x) (k : RatValue φ b y) : RatValue φ (sub a b) (x-y) := by
  change Denotes _ _ (algebraMap ℚ K0 (x-y)); rw [map_sub]; exact Denotes.sub h k
theorem mul (h : RatValue φ a x) (k : RatValue φ b y) : RatValue φ (mul a b) (x*y) := by
  change Denotes _ _ (algebraMap ℚ K0 (x*y)); rw [map_mul]; exact Denotes.mul h k
theorem div (h : RatValue φ a x) (k : RatValue φ b y) : RatValue φ (div a b) (x/y) := by
  change Denotes _ _ (algebraMap ℚ K0 (x/y)); rw [map_div₀]; exact Denotes.div h k
theorem power (h : RatValue φ a x) (k : ℕ) : RatValue φ (power a k) (x^k) := by
  change Denotes _ _ (algebraMap ℚ K0 (x^k)); rw [map_pow]; exact Denotes.power h k
theorem product {I : Type*} (s : Finset I) (f : I → E R) (g : I → ℚ)
    (h : ∀ i, RatValue φ (f i) (g i)) : RatValue φ (prodSet s f) (∏ i ∈ s,g i) := by
  change Denotes _ _ (algebraMap ℚ K0 (∏ i ∈ s,g i))
  rw [map_prod]
  exact prod_spec φ _ _ _ h
end RatValue

def βcode (x : E R) := add (mul (rat 2) (power x 2)) (rat 3)
theorem beta_correct {φ : R →+* ℚ} {e : E R} {x : ℚ} (h : RatValue φ e x) :
    RatValue φ (βcode e) (beta x) := RatValue.add (RatValue.mul (RatValue.rat φ 2) (RatValue.power h 2)) (RatValue.rat φ 3)

def rad (b : E R) :=
  mul (mul (mul (mul b (sub b (rat 1))) (sub b (rat 2401))) (add (mul (rat 32) b) (rat 343)))
    (sub (mul (rat 2) b) (rat 1))

theorem rad_correct {φ : R →+* ℚ} {b : E R} {B : ℚ} (h : RatValue φ b B) :
    RatValue φ (rad b) (scalarRadicand B) := by
  exact RatValue.mul (RatValue.mul (RatValue.mul (RatValue.mul h (RatValue.sub h (RatValue.rat φ 1)))
    (RatValue.sub h (RatValue.rat φ 2401))) (RatValue.add (RatValue.mul (RatValue.rat φ 32) h)
    (RatValue.rat φ 343))) (RatValue.sub (RatValue.mul (RatValue.rat φ 2) h) (RatValue.rat φ 1))

def markProd (t : E R) := prodSet marks (fun a => sub t (rat a))

theorem marks_correct {φ : R →+* ℚ} {t : E R} {T : ℚ} (h : RatValue φ t T) :
    RatValue φ (markProd t) (fiveProduct T) := RatValue.product _ _ _ (fun a => RatValue.sub h (RatValue.rat φ a))

def detection (a t : E R) := div (markProd t) (mul (power a 5) (power (sub t (rat 3)) 6))

theorem detector_correct {φ : R →+* ℚ} {a t : E R} {A T : ℚ} (ha : RatValue φ a A) (ht : RatValue φ t T) :
    RatValue φ (detection a t) (detector A T) :=
  RatValue.div (marks_correct ht) (RatValue.mul (RatValue.power ha 5) (RatValue.power (RatValue.sub ht (RatValue.rat φ 3)) 6))

def weight (r : E R) (g : OrdinaryTest → E R) : E R :=
  prodSet Finset.univ fun i => add (lit 1) (mul r (power (div (g i) (power r (orderRequired i))) 2))

theorem weight_correct {φ : R →+* ℚ} {r : E R} {v : K0} {g : OrdinaryTest → E R} {d : OrdinaryTest → K0}
    (hr : Denotes φ r v) (hd : ∀ i, Denotes φ (g i) (d i)) :
    Denotes φ (weight r g) (weightProduct v d orderRequired) :=
  prod_spec φ _ _ _ (fun i => Denotes.add (lit_spec φ 1)
    (Denotes.mul hr (Denotes.power (Denotes.div (hd i) (Denotes.power hr (orderRequired i))) 2)))

def normalizedEntries (p : Codes R) (M : ℕ) (c : ℤ) (b t : E R) (i : OrdinaryTest) : E R :=
  div (ordinary p M c b i) (power (sub t (rat 3)) (orderRequired i+1))

def trace (p : Codes R) (M : ℕ) (c : ℤ) (b a t : E R) : E R :=
  let d := normalizedEntries p M c b t
  let r := detection a t
  add (div (lit 1) (weight r d)) (div (lit 1) (weight r (fun i => conj (d i))))

theorem trace_correct {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (hp : Inputs φ p w)
    (M : ℕ) (c : ℤ) {b a t : E R} {β A T : ℚ} (hb : RatValue φ b β) (ha : RatValue φ a A) (ht : RatValue φ t T) :
    RatValue φ (trace p M c b a t) (ordinaryTraceAt w M c β A T) := by
  let d := fun i => ordinaryAt w M c β i / (algebraMap ℚ K0 (T-3))^(orderRequired i+1)
  have entry (i) : Denotes φ (normalizedEntries p M c b t i) (d i) :=
    Denotes.div (ordinary_spec hp M c hb i) (Denotes.power (RatValue.sub ht (RatValue.rat φ 3)) _)
  change Denotes _ _ (algebraMap ℚ K0 (ordinaryTrace (detector A T) d orderRequired))
  rw [ordinaryTrace_eq conjugation conjugation_nontrivial]
  have hr := detector_correct ha ht
  simpa only [trace,one_div] using Denotes.add
    (Denotes.div (lit_spec φ (1:K0)) (weight_correct hr entry))
    (Denotes.div (lit_spec φ (1:K0)) (weight_correct hr fun i => Denotes.conj (entry i)))

def ordinaryB (p : Codes R) (M : ℕ) (c : ℤ) (b a t : E R) : E R :=
  div (detection a t) (power (trace p M c b a t) 2)

theorem ordinaryB_correct {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (hp : Inputs φ p w)
    (M : ℕ) (c : ℤ) {b a t : E R} {β A T : ℚ} (hb : RatValue φ b β) (ha : RatValue φ a A) (ht : RatValue φ t T) :
    RatValue φ (ordinaryB p M c b a t) (detector A T/(ordinaryTraceAt w M c β A T)^2) :=
  RatValue.div (detector_correct ha ht) (RatValue.power (trace_correct hp M c hb ha ht) 2)

def six (p : Codes R) (M : ℕ) : Fin 6 → E R :=
  let H := recip (.pure p.h)
  let Q := rsc p M
  let B := recip Q
  let z := div (param Q) (param (.pure p.h))
  ![realPart H,imagPart H,realPart B,imagPart B,realPart z,imagPart z]

theorem six_correct {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (hp : Inputs φ p w)
    (M : ℕ) (i : Fin 6) : RatValue φ (six p M i) (scalarEntries w M i) := by
  have h := recip_spec φ (q:=.pure p.h) hp.h
  have r := recip_spec φ (hp.rsc M)
  have z := Denotes.div (param_spec φ (hp.rsc M)) (param_spec φ (q:=.pure p.h) hp.h)
  fin_cases i <;> first | exact Denotes.realPart h | exact Denotes.imagPart h |
    exact Denotes.realPart r | exact Denotes.imagPart r | exact Denotes.realPart z | exact Denotes.imagPart z

def nd (r a b : E R) := add (power a 2) (mul r (power b 2))

private theorem node_correct {φ : R →+* ℚ} {r a b : E R} {v x y : ℚ}
    (h : RatValue φ r v) (p : RatValue φ a x) (q : RatValue φ b y) :
    RatValue φ (nd r a b) (node v x y) := RatValue.add (RatValue.power p 2) (RatValue.mul h (RatValue.power q 2))

def tree (p : Codes R) (M : ℕ) (r : E R) : E R :=
  let g := six p M
  nd r (nd r (nd r (rat 1) (div (g 0) r)) (nd r (div (g 1) r) (div (g 2) r)))
    (nd r (div (g 3) r) (nd r (div (g 4) (power r 48)) (div (g 5) (power r 48))))

theorem tree_correct {φ : R →+* ℚ} {p : Codes R} {w : NinePoints} (hp : Inputs φ p w)
    (M : ℕ) {r : E R} {v : ℚ} (hr : RatValue φ r v) :
    RatValue φ (tree p M r) (scalarTree v (scalarEntries w M)) := by
  have e := six_correct hp M
  have d := RatValue.power hr 48
  exact node_correct hr (node_correct hr (node_correct hr (RatValue.rat φ 1) (RatValue.div (e 0) hr))
    (node_correct hr (RatValue.div (e 1) hr) (RatValue.div (e 2) hr)))
    (node_correct hr (RatValue.div (e 3) hr) (node_correct hr (RatValue.div (e 4) d) (RatValue.div (e 5) d)))

def sign (positive : Bool) : ℚ := if positive then 1 else -1

def scalarB (r Γ t : E R) (D : ℕ) (positive : Bool) : E R :=
  let s := mul (rat (sign positive)) r
  mul (power (mul (div Γ (add (rat 1) (mul (rat D) (power s 2)))) t) 2) s

theorem scalarB_correct {φ : R →+* ℚ} {r Γ t : E R} {v γ z : ℚ}
    (hr : RatValue φ r v) (hΓ : RatValue φ Γ γ) (ht : RatValue φ t z) (D : ℕ) (positive : Bool) :
    RatValue φ (scalarB r Γ t D positive) (signedValue v (sign positive) γ D z) := by
  have s := RatValue.mul (RatValue.rat φ (sign positive)) hr
  exact RatValue.mul (RatValue.power (RatValue.mul (RatValue.div hΓ (RatValue.add (RatValue.rat φ 1)
    (RatValue.mul (RatValue.rat φ D) (RatValue.power s 2)))) ht) 2) s

end
#print axioms rad_correct
#print axioms ordinaryB_correct
#print axioms trace_correct
#print axioms six_correct
#print axioms tree_correct
#print axioms scalarB_correct
end Sun28.TraceAtlas
