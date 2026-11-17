import ScalarTree

namespace Sun28.ScalarDepth
open Sun28.ScalarHeight Sun28.ScalarTrace Sun28.Scalar
variable {F : Type*} [Field F]

/-- A denominator of order kR gives the exact integral lower bound (k−1)R+1. -/
private theorem deep_leaf (v : AddValuation F (WithTop ℤ)) {r a : F} {R : ℤ}
    (hr : v r=(R:WithTop ℤ)) {k : ℕ} (bound : ((-R:ℤ):WithTop ℤ)<v (a/r^k)) :
    ((((k:ℤ)-1)*R+1:ℤ):WithTop ℤ)≤v a := by
  rcases eq_or_ne a 0 with rfl|nz
  · simp
  obtain ⟨d,hd⟩ := finite_order v nz
  rw [v.map_div,v.map_pow,hr,hd,←WithTop.coe_nsmul] at bound
  have h : -R < d-(k:ℤ)*R := by exact_mod_cast bound
  rw [hd,WithTop.coe_le_coe]
  rw [sub_mul,one_mul]
  omega

/-- The literal last two coordinate tests retain the odd contact order. -/
theorem weighted_tree (v : AddValuation F (WithTop ℤ)) {r : F} {R : ℤ} (g : Fin 6 → F)
    (hr : v r=(R:WithTop ℤ)) (positive : 0<R) (odd : Odd R)
    (bound : ((-R:ℤ):WithTop ℤ)<v (scalarTree r g)) :
    (1:WithTop ℤ)≤v (g 0) ∧ (1:WithTop ℤ)≤v (g 1) ∧
    ((47*R+1:ℤ):WithTop ℤ)≤v (g 4) ∧ ((47*R+1:ℤ):WithTop ℤ)≤v (g 5) := by
  have first := scalarTree_orders v g hr positive odd bound
  obtain ⟨_,right⟩ := low_children v hr positive odd bound
  obtain ⟨_,lower⟩ := low_children v hr positive odd right
  have last := low_children v hr positive odd lower
  exact ⟨first.1,first.2.1,deep_leaf v hr last.1,deep_leaf v hr last.2⟩

end Sun28.ScalarDepth
#print axioms Sun28.ScalarDepth.weighted_tree
