import LocalSelection

/-! Congruence of the scalar norm tree on its actual six rational leaves. -/
namespace Sun28.ScalarPlaces
open Sun28.ScalarHeight Sun28.ScalarTrace
open WithZero
noncomputable section

variable {F : Type*} [Field F]

/-- A leaf in the maximal ideal remains there under squaring and in either
argument of the quadratic node when the radicand is integral. -/
theorem node_small (v : AddValuation F (WithTop ℤ)) {r x y : F}
    (hr : 0≤v r) (hx : 1≤v x) (hy : 1≤v y) : 1≤v (node r x y) := by
  have square {z : F} (hz : 1≤v z) : 1≤v (z^2) := by
    rw [v.map_pow,two_nsmul]
    exact hz.trans (le_add_of_nonneg_right ((by decide : (0:WithTop ℤ)≤1).trans hz))
  apply v.map_le_add (square hx)
  rw [v.map_mul]
  exact (square hy).trans (le_add_of_nonneg_left hr)

/-- The left unit in the tree survives each successive node. -/
theorem node_one (v : AddValuation F (WithTop ℤ)) {r x y : F}
    (hr : 0≤v r) (hx : 1≤v (x-1)) (hy : 1≤v y) : 1≤v (node r x y-1) := by
  have hpos : v (1:F)<v (x-1) := by
    rw [v.map_one]; exact (by decide : (0:WithTop ℤ)<1).trans_le hx
  have hu : v x=0 := by simpa using v.map_eq_of_lt_sub hpos
  have hi : 0≤v (x+1) := v.map_le_add hu.ge v.map_one.ge
  have identity : node r x y-1=(x-1)*(x+1)+r*y^2 := by unfold node; ring
  rw [identity]
  apply v.map_le_add
  · rw [v.map_mul]; exact hx.trans (le_add_of_nonneg_right hi)
  · rw [v.map_mul,v.map_pow,two_nsmul]
    exact (hy.trans (le_add_of_nonneg_right ((by decide : (0:WithTop ℤ)≤1).trans hy))).trans
      (le_add_of_nonneg_left hr)

/-- Exponent of the radicand dividing each stored scalar coefficient. -/
def leafPower (i : Fin 6) : ℕ := if i.val<4 then 1 else 48

theorem tree_congruent_one (v : AddValuation F (WithTop ℤ)) {r : F} {g : Fin 6→F}
    (hr : 0≤v r) (leaves : ∀ i, 1≤v (g i/r^(leafPower i))) :
    1≤v (scalarTree r g-1) := by
  apply node_one v hr
  · apply node_one v hr
    · apply node_one v hr
      · simp
      · simpa [leafPower] using leaves 0
    · apply node_small v hr
      · simpa [leafPower] using leaves 1
      · simpa [leafPower] using leaves 2
  · apply node_small v hr
    · simpa [leafPower] using leaves 3
    · apply node_small v hr
      · simpa [leafPower] using leaves 4
      · simpa [leafPower] using leaves 5

def ratOrder (p : ℕ) [Fact p.Prime] : AddValuation ℚ (WithTop ℤ) :=
  discreteOrder (Rat.padicValuation p)

theorem rat_order_value {p : ℕ} [Fact p.Prime] {x : ℚ} (hx : x≠0) :
    ratOrder p x=((padicValRat p x:ℤ):WithTop ℤ) := by
  change (if Rat.padicValuation p x=0 then ⊤ else ((-WithZero.log (Rat.padicValuation p x):ℤ):WithTop ℤ))=_
  simp [Rat.padicValuation,hx]

theorem rat_tree_unit {p : ℕ} [Fact p.Prime] {r : ℤ} {g : Fin 6→ℚ}
    (leaves : ∀ i, 1≤ratOrder p (g i/(r:ℚ)^(leafPower i))) :
    scalarTree (r:ℚ) g≠0 ∧ padicValRat p (scalarTree (r:ℚ) g)=0 := by
  let v := ratOrder p
  have integral : 0≤v (r:ℚ) := by
    by_cases h : r=0
    · simp [h,v]
    rw [show v (r:ℚ)=_ from rat_order_value (p:=p) (Int.cast_ne_zero.mpr h),padicValRat.of_int]
    exact WithTop.coe_le_coe.mpr (Int.natCast_nonneg _)
  have h := tree_congruent_one v integral leaves
  have hpos : v (1:ℚ)<v (scalarTree (r:ℚ) g-1) := by
    rw [v.map_one]; exact (by decide : (0:WithTop ℤ)<1).trans_le h
  have hu : v (scalarTree (r:ℚ) g)=0 := by simpa using v.map_eq_of_lt_sub hpos
  have nz : scalarTree (r:ℚ) g≠0 := (AddValuation.ne_top_iff v).mp (by rw [hu]; exact WithTop.coe_ne_top)
  refine ⟨nz,?_⟩
  change ratOrder p _=0 at hu
  rw [rat_order_value nz] at hu
  exact_mod_cast hu
end
end Sun28.ScalarPlaces
#print axioms Sun28.ScalarPlaces.node_small
#print axioms Sun28.ScalarPlaces.node_one
#print axioms Sun28.ScalarPlaces.tree_congruent_one
#print axioms Sun28.ScalarPlaces.rat_order_value
#print axioms Sun28.ScalarPlaces.rat_tree_unit
