import PartitionOrders
import RationalBranchHeight

/-! Projective coordinate changes preserve the ratios of triple-partition weights. -/
namespace ZInQBlueprint.BranchDepth
open BranchFormula BranchHeight ThetaPeriod
noncomputable section
variable {K : Type*} [Field K]

def mobius (a b c d x : K) := (a*x+b)/(c*x+d)

theorem difference_mobius (a b c d x y : K) (hx : c*x+d≠0) (hy : c*y+d≠0) :
    (mobius a b c d x-mobius a b c d y)*(c*x+d)*(c*y+d)=(a*d-b*c)*(x-y) := by
  unfold mobius
  let m := c*x+d
  let n := c*y+d
  change ((a*x+b)/m - (a*y+b)/n)*m*n = _
  have hm : m ≠ 0 := hx
  have hn : n ≠ 0 := hy
  rw [sub_mul,sub_mul,div_mul_cancel₀ _ hm]
  have e : (a*y+b)/n*m*n=(a*y+b)*m := by rw [mul_right_comm,div_mul_cancel₀ _ hn]
  rw [e]
  dsimp [m,n]
  ring

private theorem clear_triangle (r : Fin 6 → K) (a b c d : K) (hu : ∀ i, c*r i+d≠0)
    (i j k : Fin 6) :
    triangle (fun s => mobius a b c d (r s)) i j k *
      ((c*r i+d)*(c*r j+d)*(c*r k+d))^2 = (a*d-b*c)^3 * triangle r i j k := by
  unfold triangle
  calc
    _ = ((mobius a b c d (r i)-mobius a b c d (r j))*(c*r i+d)*(c*r j+d)) *
        ((mobius a b c d (r i)-mobius a b c d (r k))*(c*r i+d)*(c*r k+d)) *
        ((mobius a b c d (r j)-mobius a b c d (r k))*(c*r j+d)*(c*r k+d)) := by ring
    _ = _ := by rw [difference_mobius _ _ _ _ _ _ (hu i) (hu j),
                    difference_mobius _ _ _ _ _ _ (hu i) (hu k),
                    difference_mobius _ _ _ _ _ _ (hu j) (hu k)]; ring

private theorem row_product {M : Type*} [CommRing M] (h : Fin 6 → M) (i : Fin 10) :
    (h (row i).p.castSucc * h (row i).q.castSucc * h 5) *
    (h (row i).a.castSucc * h (row i).b.castSucc * h (row i).c.castSucc) = ∏ j, h j := by
  have hprod : (∏ j, h j) = h 0*h 1*h 2*h 3*h 4*h 5 := by
    simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
    change h 0*(h 1*(h 2*(h 3*(h 4*h 5)))) = _
    ring
  rw [hprod]
  fin_cases i <;> dsimp [row] <;> ring

theorem clear_weight_mobius (r : Fin 6 → K) (a b c d : K) (hu : ∀ i, c*r i+d≠0) (i : Fin 10) :
    weight (fun j => mobius a b c d (r j)) i * (∏ j, (c*r j+d))^4 =
      (a*d-b*c)^12 * weight r i := by
  rw [← row_product (fun j => c*r j+d) i]
  dsimp only [weight]
  let t := row i
  have h₁ := clear_triangle r a b c d hu t.p.castSucc t.q.castSucc 5
  have h₂ := clear_triangle r a b c d hu t.a.castSucc t.b.castSucc t.c.castSucc
  have regroup (x y A B : K) : (x*y)^2*(A*B)^4 = ((x*A^2)*(y*B^2))^2 := by ring
  rw [regroup,h₁,h₂]
  ring

theorem ratio_mobius (r : Fin 6 → K) (a b c d : K) (hd : a*d-b*c≠0)
    (hu : ∀ i, c*r i+d≠0) (i j : Fin 10) :
    weight (fun k => mobius a b c d (r k)) i / weight (fun k => mobius a b c d (r k)) j =
    weight r i / weight r j := by
  let D := (∏ k, (c*r k+d))^4
  have hD : D≠0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ => hu k)
  let e := fun i => clear_weight_mobius r a b c d hu i
  rw [← mul_div_mul_right _ _ hD,e i,e j,mul_div_mul_left _ _ (pow_ne_zero 12 hd)]

theorem projective_branch_ratio {r : Fin 6 → ℂ} (hr : Function.Injective r) (i : Fin 10) :
    branchRatio r i = weight r i / weight r 0 := by
  unfold branchRatio
  rw [← mul_div_mul_right _ _ (pow_ne_zero 4 (denominator_ne hr)),clear_row hr,clear_row hr]
  rfl

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.difference_mobius
#print axioms ZInQBlueprint.BranchDepth.clear_weight_mobius
#print axioms ZInQBlueprint.BranchDepth.ratio_mobius
#print axioms ZInQBlueprint.BranchDepth.projective_branch_ratio
