import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic

/-! Odd valuations of the two factors in Sun's scalar test. -/
namespace Sun28.ScalarTrace
variable {K : Type*} [Field K]

def factor (r D : K) (k : ℕ) := 1 + r*(D/r^k)^2

def weight (r x y : K) := factor r x 1 * factor r y 48

def average (u w : K) := (u⁻¹+w⁻¹)/2

/-- A finite integer version of the valuation of a test factor together with
the information it gives on the test. The test itself may vanish. -/
theorem factor_order (v : AddValuation K (WithTop ℤ)) {r D : K} {α : ℤ}
    (hr : v r = (α:WithTop ℤ)) (ho : Odd α) (k : ℕ) :
    ∃ l : ℤ, v (factor r D k) = (l:WithTop ℤ) ∧ l ≤ 0 ∧
      (D=0 ∨ ∃ d : ℤ, v D = (d:WithTop ℤ) ∧ l ≤ α+2*(d-(k:ℤ)*α)) := by
  by_cases hd : D=0
  · exact ⟨0,by simp [factor,hd],by omega,Or.inl hd⟩
  obtain ⟨d,he⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr hd)
  have hD : v D = (d:WithTop ℤ) := he.symm
  let b := α+2*(d-(k:ℤ)*α)
  have hv : v (r*(D/r^k)^2) = (b:WithTop ℤ) := by
    simp only [AddValuation.map_mul,AddValuation.map_div,AddValuation.map_pow,hr,hD,
      ←WithTop.coe_nsmul]
    congr 1
  have hn : (0:ℤ) ≠ b := by obtain ⟨a,ha⟩ := ho; dsimp [b]; omega
  have hh : v (1:K) ≠ v (r*(D/r^k)^2) := by rw [v.map_one,hv]; exact_mod_cast hn
  refine ⟨min 0 b,?_,min_le_left ..,Or.inr ⟨d,hD,min_le_right ..⟩⟩
  unfold factor
  rw [v.map_add_of_distinct_val hh,v.map_one,hv]
  exact_mod_cast (rfl : min (0:ℤ) b=min 0 b)

/-- The total order of the product bounds the order of each of its two factors. -/
theorem weight_order (v : AddValuation K (WithTop ℤ)) {r x y : K} {α : ℤ}
    (hr : v r=(α:WithTop ℤ)) (ho : Odd α) :
    ∃ l : ℤ, v (weight r x y)=(l:WithTop ℤ) ∧ l ≤ 0 ∧
      (x=0 ∨ ∃ d : ℤ, v x=(d:WithTop ℤ) ∧ l ≤ 2*d-α) ∧
      (y=0 ∨ ∃ d : ℤ, v y=(d:WithTop ℤ) ∧ l ≤ 2*d-95*α) := by
  obtain ⟨l,hl,hln,hx⟩ := factor_order (D:=x) v hr ho 1
  obtain ⟨m,hm,hmn,hy⟩ := factor_order (D:=y) v hr ho 48
  refine ⟨l+m,?_,by omega,?_,?_⟩
  · rw [weight,v.map_mul,hl,hm,WithTop.coe_add]
  · rcases hx with hx | ⟨d,hd,he⟩
    · exact Or.inl hx
    · exact Or.inr ⟨d,hd,by norm_num at he; omega⟩
  · rcases hy with hy | ⟨d,hd,he⟩
    · exact Or.inl hy
    · exact Or.inr ⟨d,hd,by norm_num at he; omega⟩

/-- At the selected place the unrounded inequalities are retained as integers. -/
def Precise (v : AddValuation K (WithTop ℤ)) (α : ℤ) (x y : K) : Prop :=
    (x=0 ∨ ∃ d : ℤ, v x=(d:WithTop ℤ) ∧ α+1 ≤ 4*d) ∧
    (y=0 ∨ ∃ d : ℤ, v y=(d:WithTop ℤ) ∧ 189*α+1 ≤ 4*d)

theorem Precise.orders {v : AddValuation K (WithTop ℤ)} {α : ℤ} {x y : K}
    (h : Precise v α x y) (ha : 0 < α) :
    (1:WithTop ℤ) ≤ v x ∧ (48:WithTop ℤ) ≤ v y := by
  obtain ⟨h₁,h₂⟩ := h
  constructor
  · rcases h₁ with rfl | ⟨d,hd,hi⟩
    · simp
    · rw [hd]; exact_mod_cast (show (1:ℤ) ≤ d by omega)
  · rcases h₂ with rfl | ⟨d,hd,hi⟩
    · simp
    · rw [hd]; exact WithTop.coe_le_coe.mpr (show (48:ℤ) ≤ d by omega)

/-- Products at two conjugate embeddings are actual field values. A positive
odd scalar valuation forces both precisions at the same embedding. -/
theorem average_soundness (v : AddValuation K (WithTop ℤ)) {r x y x' y' A : K} {α : ℤ}
    (hr : v r=(α:WithTop ℤ)) (ho : Odd α) (htwo : v (2:K)=0)
    (hA : v A=0)
    (hθ : average (weight r x y) (weight r x' y') ≠ 0)
    (hint : (0:WithTop ℤ) ≤ v (A^2*r/(average (weight r x y) (weight r x' y'))^2)) :
    0 < α ∧ (Precise v α x y ∨ Precise v α x' y') := by
  let W := weight r x y
  let W' := weight r x' y'
  let θ := average W W'
  obtain ⟨t,ht'⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr hθ)
  have ht : v θ=(t:WithTop ℤ) := ht'.symm
  have hi : 0 ≤ α-2*t := by
    change (0:WithTop ℤ) ≤ v (A^2*r/θ^2) at hint
    simp only [AddValuation.map_mul,AddValuation.map_div,AddValuation.map_pow,hA,hr,ht,
      nsmul_zero,zero_add,←WithTop.coe_nsmul] at hint
    exact_mod_cast hint
  have hip : 1 ≤ α-2*t := by obtain ⟨i,hh⟩ := ho; omega
  obtain ⟨l,hl,hln,hx,hy⟩ := weight_order (x:=x) (y:=y) v hr ho
  obtain ⟨m,hm,hmn,hx',hy'⟩ := weight_order (x:=x') (y:=y') v hr ho
  have hmin := v.map_add W⁻¹ W'⁻¹
  have hav : v (W⁻¹+W'⁻¹)=(t:WithTop ℤ) := by
    change v ((W⁻¹+W'⁻¹)/2)=(t:WithTop ℤ) at ht
    simpa [AddValuation.map_div,htwo] using ht
  rw [hav, v.map_inv,v.map_inv, show v W = (l:WithTop ℤ) from hl,
    show v W' = (m:WithTop ℤ) from hm, ←WithTop.LinearOrderedAddCommGroup.coe_neg,←WithTop.LinearOrderedAddCommGroup.coe_neg] at hmin
  have hh : min (-l) (-m) ≤ t := by exact_mod_cast hmin
  have one {u w : K} {s : ℤ} (hs : -s ≤ t)
      (hu : u=0 ∨ ∃ d : ℤ, v u=(d:WithTop ℤ) ∧ s ≤ 2*d-α)
      (hw : w=0 ∨ ∃ d : ℤ, v w=(d:WithTop ℤ) ∧ s ≤ 2*d-95*α) :
      Precise v α u w := by
    constructor
    · rcases hu with z | ⟨d,hd,he⟩
      · exact Or.inl z
      · exact Or.inr ⟨d,hd,by omega⟩
    · rcases hw with z | ⟨d,hd,he⟩
      · exact Or.inl z
      · exact Or.inr ⟨d,hd,by omega⟩
  rcases min_le_iff.mp hh with h | h
  · exact ⟨by omega,Or.inl (one h hx hy)⟩
  · exact ⟨by omega,Or.inr (one h hx' hy')⟩

end Sun28.ScalarTrace
#print axioms Sun28.ScalarTrace.factor_order
#print axioms Sun28.ScalarTrace.weight_order
#print axioms Sun28.ScalarTrace.Precise.orders
#print axioms Sun28.ScalarTrace.average_soundness
