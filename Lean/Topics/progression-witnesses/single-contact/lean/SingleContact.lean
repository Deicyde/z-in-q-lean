import Std

namespace ProgressionWitnesses.SingleContact

/-- Parity in the integral normalization of the valuation. -/
def OddOrder (α : Int) : Prop := ∃ k : Int, α = 2*k + 1

/-- Only the usual unequal-valuation rule and the multiplicative laws are used.
    The value of zero is deliberately unconstrained and never used. -/
structure RationalOrder where
  ord : Rat → Int
  one : ord 1 = 0
  neg : ∀ x : Rat, x ≠ 0 → ord (-x) = ord x
  mul : ∀ a b : Rat, a ≠ 0 → b ≠ 0 → ord (a*b) = ord a + ord b
  div : ∀ a b : Rat, a ≠ 0 → b ≠ 0 → ord (a/b) = ord a - ord b
  addUnequal : ∀ a b : Rat, a ≠ 0 → b ≠ 0 → ord a ≠ ord b →
    a+b ≠ 0 ∧ ord (a+b) = min (ord a) (ord b)

/-- For any rational k the quotient exists, is nonzero, and has order zero.
    For k ≠ 0 both signs have order min(0, ord R + 2 ord k). -/
theorem ratio_unit (v : RationalOrder) (R k : Rat) (hR : R ≠ 0)
    (odd : OddOrder (v.ord R)) :
    1-R*k^2 ≠ 0 ∧ 1+R*k^2 ≠ 0 ∧ v.ord ((1-R*k^2)/(1+R*k^2)) = 0 := by
  by_cases hk : k = 0
  · subst k
    have hm : (1:Rat)-R*(0:Rat)^2=1 := by grobner
    have hp : (1:Rat)+R*(0:Rat)^2=1 := by grobner
    rw [hm, hp, v.div 1 1 (by decide) (by decide)]
    exact ⟨by decide, by decide, by omega⟩
  · have hsq : k*k ≠ 0 := by grind
    have heq : k^2 = k*k := by grobner
    have hn : R*k^2 ≠ 0 := by grind
    have hneg : -(R*k^2) ≠ 0 := by grind
    have ho : v.ord (R*k^2) = v.ord R + 2*v.ord k := by
      rw [heq, v.mul _ _ hR hsq, v.mul _ _ hk hk]
      omega
    obtain ⟨b,hb⟩ := odd
    have hu : v.ord 1 ≠ v.ord (R*k^2) := by rw [v.one,ho,hb]; omega
    have hv : v.ord (-(R*k^2)) = v.ord (R*k^2) := v.neg _ hn
    have hp := v.addUnequal 1 (R*k^2) (by decide) hn hu
    have hm := v.addUnequal 1 (-(R*k^2)) (by decide) hneg (hv ▸ hu)
    rw [Rat.sub_eq_add_neg]
    refine ⟨hm.1, hp.1, ?_⟩
    rw [v.div _ _ hm.1 hp.1, hm.2, hp.2, hv]
    omega

/-- Clearing two factors of equal order forces b and T nonzero and gives
    the exact order of b before making any division. -/
theorem cleared_pole (v : RationalOrder) {R U V T b : Rat} (hR : R ≠ 0)
    (hU : U ≠ 0) (hV : V ≠ 0) (unitRatio : v.ord U = v.ord V)
    (cleared : b*T^2*U = R*V) :
    b ≠ 0 ∧ T ≠ 0 ∧ v.ord b = v.ord R - 2*v.ord T := by
  have hb : b ≠ 0 := by grind
  have hT : T ≠ 0 := by grind
  have sq : T^2 = T*T := by grobner
  have hs : T*T ≠ 0 := by grind
  have hp : b*(T*T) ≠ 0 := by grind
  have value := congrArg v.ord cleared
  rw [sq, v.mul _ _ hp hU, v.mul _ _ hb hs, v.mul _ _ hT hT, v.mul _ _ hR hV] at value
  exact ⟨hb,hT,by omega⟩

theorem corrected_pole (v : RationalOrder) {R k T b : Rat} (hR : R ≠ 0)
    (odd : OddOrder (v.ord R)) (cleared : b*T^2*(1+R*k^2) = R*(1-R*k^2)) :
    b ≠ 0 ∧ T ≠ 0 ∧ v.ord b = v.ord R - 2*v.ord T := by
  obtain ⟨hm,hp,hu⟩ := ratio_unit v R k hR odd
  rw [v.div _ _ hm hp] at hu
  exact cleared_pole v hR hp hm (by omega) cleared

/-- The squared unit in the single-contact polynomial. -/
theorem corrected_pole_square (v : RationalOrder) {R k T b : Rat} (hR : R ≠ 0)
    (odd : OddOrder (v.ord R)) (cleared : b*T^2*(1+R*k^2)^2 = R*(1-R*k^2)^2) :
    b ≠ 0 ∧ T ≠ 0 ∧ v.ord b = v.ord R - 2*v.ord T := by
  obtain ⟨hm,hp,hu⟩ := ratio_unit v R k hR odd
  rw [v.div _ _ hm hp] at hu
  apply cleared_pole v hR (by grind) (by grind) _ cleared
  rw [show (1+R*k^2)^2 = (1+R*k^2)*(1+R*k^2) by grobner,
      show (1-R*k^2)^2 = (1-R*k^2)*(1-R*k^2) by grobner, v.mul _ _ hp hp, v.mul _ _ hm hm]
  omega

/-- wMax is the maximum of the product orders.  tr=v(T) and b=v(B). -/
theorem positive_pole {α wMax tr b : Int} (odd : OddOrder α) (nonpos : wMax ≤ 0)
    (traceBound : -wMax ≤ tr) (pole : b = α - 2*tr) (integral : 0 ≤ b) :
    0 < α ∧ 0 < α+2*wMax := by
  obtain ⟨k,hk⟩ := odd
  omega

/-- The factor bound is taken at the maximizing place. -/
theorem sharp_depth {α wMax tr b m y : Int} (odd : OddOrder α) (nonpos : wMax ≤ 0)
    (traceBound : -wMax ≤ tr) (pole : b = α - 2*tr) (integral : 0 ≤ b)
    (factor : wMax ≤ min 0 ((1-2*m)*α+2*y)) : (4*m-3)*α < 4*y := by
  have pos := (positive_pole odd nonpos traceBound pole integral).2
  have upper := Int.le_trans factor (Int.min_le_right 0 ((1-2*m)*α+2*y))
  rw [Int.sub_mul, Int.one_mul, Int.mul_assoc] at upper
  rw [Int.sub_mul, Int.mul_assoc]
  omega

theorem depth {α wMax tr b m y : Int} (odd : OddOrder α) (nonpos : wMax ≤ 0)
    (traceBound : -wMax ≤ tr) (pole : b = α - 2*tr) (integral : 0 ≤ b)
    (order : 1 ≤ m) (factor : wMax ≤ min 0 ((1-2*m)*α+2*y)) : m ≤ y := by
  have sharp := sharp_depth odd nonpos traceBound pole integral factor
  have pos := (positive_pole odd nonpos traceBound pole integral).1
  have hm : 0 ≤ 4*m - 3 := by omega
  have lower := Int.mul_le_mul_of_nonneg_left (show 1 ≤ α by omega) hm
  rw [Int.mul_one] at lower
  omega

/-- A zero field test has infinite order; nonzero tests carry an integer order. -/
def DepthAtLeast (m : Int) : Option Int → Prop
  | none => True
  | some y => m ≤ y

/-- On a finite set of places, one and the same maximizing place works for
    every test (even if there are infinitely many test indices). -/
theorem one_place {Place Test : Type} (places : List Place) (w : Place → Int)
    (Y : Place → Test → Option Int) (order : Test → Int) {α wMax tr b : Int}
    (maximum : (places.map w).max? = some wMax)
    (nonpos : ∀ v ∈ places, w v ≤ 0) (odd : OddOrder α)
    (traceBound : -wMax ≤ tr) (pole : b = α - 2*tr) (integral : 0 ≤ b)
    (positiveOrders : ∀ i, 1 ≤ order i)
    (factors : ∀ v ∈ places, ∀ i y, Y v i = some y →
      w v ≤ min 0 ((1-2*order i)*α+2*y)) :
    0 < α ∧ ∃ v ∈ places, w v = wMax ∧ ∀ i, DepthAtLeast (order i) (Y v i) := by
  letI : Std.MaxEqOr Int := ⟨by
    intro a b
    by_cases h : a ≤ b
    · exact Or.inr (Int.max_eq_right h)
    · exact Or.inl (Int.max_eq_left (by omega))⟩
  obtain ⟨v,hv,hmax⟩ := List.mem_map.mp (List.max?_mem maximum)
  have hwMax : wMax ≤ 0 := hmax ▸ nonpos v hv
  refine ⟨(positive_pole odd hwMax traceBound pole integral).1,v,hv,hmax,?_⟩
  intro i
  cases hi : Y v i with
  | none => trivial
  | some y =>
    exact depth odd hwMax traceBound pole integral (positiveOrders i) (hmax ▸ factors v hv i y hi)

#print axioms ratio_unit
#print axioms cleared_pole
#print axioms corrected_pole
#print axioms corrected_pole_square
#print axioms positive_pole
#print axioms sharp_depth
#print axioms depth
#print axioms one_place

end ProgressionWitnesses.SingleContact
