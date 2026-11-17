import FormalKernelLog

/-! The single lower bound preserved by every node of the seven-leaf norm tree. -/
namespace Sun28.ScalarHeight
open Sun28.Scalar Sun28.ScalarTrace
variable {F : Type*} [Field F]

def node (r x y : F) : F := x^2+r*y^2

def scalarTree (r : F) (g : Fin 6 → F) : F :=
  node r (node r (node r 1 (g 0/r)) (node r (g 1/r) (g 2/r)))
    (node r (g 3/r) (node r (g 4/r^48) (g 5/r^48)))

theorem scalarTree_display (r : F) (g : Fin 6 → F) (rn : r≠0) :
  scalarTree r g =
    ((1+(g 0)^2/r)^2+r*((g 1)^2/r^2+(g 2)^2/r)^2)^2+
    r*((g 3/r)^2+r*((g 4)^2/r^96+(g 5)^2/r^95)^2)^2 := by
  unfold scalarTree node
  field_simp [rn]

theorem low_children (v : AddValuation F (WithTop ℤ)) {r x y : F} {R : ℤ}
    (hr : v r=(R:WithTop ℤ)) (pos : 0<R) (odd : Odd R)
    (parent : ((-R:ℤ):WithTop ℤ)<v (node r x y)) :
    ((-R:ℤ):WithTop ℤ)<v x ∧ ((-R:ℤ):WithTop ℤ)<v y := by
  have branch {a b : ℤ} (va : v x=(a:WithTop ℤ)) (vb : v y=(b:WithTop ℤ)) :
      -R<a ∧ -R<b := by
    have left : v (x^2)=((2*a:ℤ):WithTop ℤ) := by rw [v.map_pow,va]; exact_mod_cast (two_nsmul a).trans (two_mul a).symm
    have right : v (r*y^2)=((R+2*b:ℤ):WithTop ℤ) := by rw [v.map_mul,v.map_pow,hr,vb]; congr 1
    have ne : v (x^2)≠v (r*y^2) := by
      rw [left,right]
      obtain ⟨k,hk⟩ := odd
      exact_mod_cast (show 2*a≠R+2*b by omega)
    rw [node,v.map_add_of_distinct_val ne,left,right,lt_min_iff] at parent
    obtain ⟨hl,hr'⟩ := parent
    have h1 := WithTop.coe_lt_coe.mp hl
    have h2 := WithTop.coe_lt_coe.mp hr'
    omega
  by_cases xn : x=0
  · subst x
    by_cases yn : y=0
    · subst y; simp only [v.map_zero,WithTop.coe_lt_top,and_self]
    obtain ⟨b,vb⟩ := finite_order v yn
    have h : -R<R+2*b := by
      change _ < v (0^2+r*y^2) at parent
      simp only [zero_pow (by decide : 2≠0),zero_add,v.map_mul,v.map_pow,hr,vb,←WithTop.coe_nsmul,←WithTop.coe_add] at parent
      exact_mod_cast parent
    simp only [v.map_zero,WithTop.coe_lt_top,true_and,vb,WithTop.coe_lt_coe]
    omega
  by_cases yn : y=0
  · subst y
    obtain ⟨a,va⟩ := finite_order v xn
    have h : -R<2*a := by
      change _ < v (x^2+r*0^2) at parent
      simp only [zero_pow (by decide : 2≠0),mul_zero,add_zero,v.map_pow,va,←WithTop.coe_nsmul] at parent
      exact_mod_cast parent
    simp only [v.map_zero,WithTop.coe_lt_top,and_true,va,WithTop.coe_lt_coe]
    omega
  obtain ⟨a,va⟩ := finite_order v xn
  obtain ⟨b,vb⟩ := finite_order v yn
  rw [va,vb]
  exact ⟨WithTop.coe_lt_coe.mpr (branch va vb).1,WithTop.coe_lt_coe.mpr (branch va vb).2⟩

private theorem leaf_order (v : AddValuation F (WithTop ℤ)) {r a : F} {R : ℤ}
    (hr : v r=(R:WithTop ℤ)) (pos : 0<R) {k : ℕ} (kpos : 0<k)
    (leaf : ((-R:ℤ):WithTop ℤ)<v (a/r^k)) : ((k:ℤ):WithTop ℤ)≤v a := by
  rcases eq_or_ne a 0 with rfl|nz
  · simp
  obtain ⟨d,hd⟩ := finite_order v nz
  rw [v.map_div,v.map_pow,hr,hd,←WithTop.coe_nsmul] at leaf
  have h : -R < d-(k:ℤ)*R := by exact_mod_cast leaf
  have A : 0≤(k:ℤ)-1 := by omega
  have B : 0≤R-1 := by omega
  rw [hd]
  apply WithTop.coe_le_coe.mpr
  nlinarith [mul_nonneg A B]

theorem scalarTree_orders (v : AddValuation F (WithTop ℤ)) {r : F} {R : ℤ} (g : Fin 6 → F)
    (hr : v r=(R:WithTop ℤ)) (pos : 0<R) (odd : Odd R)
    (bound : ((-R:ℤ):WithTop ℤ)<v (scalarTree r g)) :
    (1:WithTop ℤ)≤v (g 0) ∧ (1:WithTop ℤ)≤v (g 1) ∧
      (48:WithTop ℤ)≤v (g 4) ∧ (48:WithTop ℤ)≤v (g 5) := by
  obtain ⟨left,right⟩ := low_children v hr pos odd bound
  obtain ⟨a,b⟩ := low_children v hr pos odd left
  obtain ⟨_,d⟩ := low_children v hr pos odd right
  have last := low_children v hr pos odd d
  refine ⟨?_,?_,leaf_order v hr pos (by decide : 0<48) last.1,leaf_order v hr pos (by decide : 0<48) last.2⟩
  · exact leaf_order v hr pos (by decide : 0<1) (by simpa using (low_children v hr pos odd a).2)
  · exact leaf_order v hr pos (by decide : 0<1) (by simpa using (low_children v hr pos odd b).1)

end Sun28.ScalarHeight
#print axioms Sun28.ScalarHeight.scalarTree_display
#print axioms Sun28.ScalarHeight.low_children
#print axioms Sun28.ScalarHeight.scalarTree_orders
