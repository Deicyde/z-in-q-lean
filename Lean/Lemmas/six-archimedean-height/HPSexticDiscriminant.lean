import OddEquation
import RootDiscriminant

/-! Root-independent algebraic discriminant of the restricted monic odd chart. -/
open Polynomial
namespace ZInQBlueprint.ArchimedeanHeight
open OddModel ThetaPeriod BranchFormula
noncomputable section

private def vFive (u : Fin 5 → ℂ) : ℂ := ∏ i, ∏ j, if i < j then u i - u j else 1

private theorem point_slope (z : Fin 5 → ℂ) (i : Fin 5) :
    (∏ j, (X - C (z j))).derivative.eval (z i) = ∏ j, (if i = j then 1 else z i - z j) := by
  rw [← Finset.mul_prod_erase _ (fun j => X - C (z j)) (Finset.mem_univ i), derivative_mul]
  simp only [eval_add,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul,add_zero,
    derivative_sub,derivative_X,derivative_C,sub_zero,one_mul,eval_prod]
  rw [← Finset.mul_prod_erase _ (fun j => if i = j then 1 else z i-z j) (Finset.mem_univ i)]
  simp only [ite_true,one_mul]
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1.symm]

private theorem slope_factor (z : Fin 5 → ℂ) (i j : Fin 5) :
    (if i = j then 1 else z i-z j) = (if j < i then -1 else 1)*
      ((if i < j then z i-z j else 1)*(if j < i then z j-z i else 1)) := by
  rcases lt_trichotomy i j with h|h|h
  · simp [h,h.ne,not_lt_of_ge h.le]
  · subst j; simp
  · simp [h,h.ne.symm,not_lt_of_ge h.le]

private theorem quintic_discriminant (r : Fin 6 → ℂ) : (quintic r).discr = (vFive (finiteBranches r))^2 := by
  let g := quintic r
  have gl : g.natDegree = 5 := (quintic_monic_degree r).2
  have gd : g.derivative.natDegree ≤ 4 := by rw [natDegree_derivative,gl]
  have hres := resultant_deriv (f:=g) (natDegree_pos_iff_degree_pos.mp (by omega))
  rw [gl,(quintic_monic_degree r).1.leadingCoeff] at hres
  norm_num at hres
  have key := resultant_prod_left Finset.univ (fun i : Fin 5 => X - C (finiteBranches r i)) g.derivative 4 (by simp) gd
  change g.resultant g.derivative g.natDegree 4 = _ at key
  rw [gl] at key
  simp only [natDegree_X_sub_C] at key
  have each (i : Fin 5) : (X-C (finiteBranches r i)).resultant g.derivative 1 4 =
      g.derivative.eval (finiteBranches r i) := resultant_X_sub_C_left _ _ _ gd
  have evals : g.resultant g.derivative 5 4 = ∏ i, g.derivative.eval (finiteBranches r i) := key.trans (Finset.prod_congr rfl (fun i _ => each i))
  clear key
  simp only [g,quintic,point_slope,slope_factor,Finset.prod_mul_distrib] at evals
  have hsign : (∏ i : Fin 5, ∏ j : Fin 5, (if j < i then -1 else 1 : ℂ)) = 1 := by
    have hh : (∏ i : Fin 5, ∏ j : Fin 5, (if j < i then -1 else 1 : ℤ)) = 1 := by decide
    have mapped := congrArg (Int.castRingHom ℂ) hh
    simpa only [map_prod,apply_ite,map_neg,map_one] using mapped
  rw [hsign,one_mul] at evals
  let a (i j : Fin 5) : ℂ := if i < j then finiteBranches r i - finiteBranches r j else 1
  change _ = (∏ i, ∏ j, a i j) * (∏ i, ∏ j, a j i) at evals
  rw [Finset.prod_comm (f:=fun i j => a j i)] at evals
  change (quintic r).resultant (quintic r).derivative 5 4 = _ at evals
  change (quintic r).resultant (quintic r).derivative 5 4 = (quintic r).discr at hres
  rw [← hres,evals,pow_two]
  rfl

private def gap (r : Fin 6 → ℂ) (i : Fin 5) := r i.castSucc-r (Fin.last 5)

private theorem six_edges (r : Fin 6 → ℂ) : vandermonde r =
    vFive (fun i => r i.castSucc) * ∏ i, gap r i := by
  let e (i j : Fin 6) : ℂ := if i < j then r i-r j else 1
  change (∏ i, ∏ j, e i j) = _
  have row (i : Fin 5) : (∏ j, e i.castSucc j) =
      (∏ j : Fin 5, if i < j then r i.castSucc-r j.castSucc else 1)*gap r i := by
    rw [Fin.prod_univ_castSucc]
    simp only [e, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, ite_true,gap]
  have last : (∏ j, e (Fin.last 5) j) = 1 := by
    exact Finset.prod_eq_one (fun j _ => by simp only [e,not_lt_of_ge (Fin.le_last j),ite_false])
  rw [Fin.prod_univ_castSucc,last,mul_one]
  simp only [row,Finset.prod_mul_distrib,vFive]

private theorem five_edge_units (u : Fin 5 → ℂ) :
    (∏ i : Fin 5, ∏ j : Fin 5, if i < j then -(u i*u j) else 1) = (∏ i, u i)^4 := by
  simp (config := { decide := true }) only [Fin.prod_univ_five,ite_true,ite_false,one_mul,mul_one]
  ring

private theorem inverse_edges (r : Fin 6 → ℂ) (hr : Function.Injective r) :
    vFive (finiteBranches r) * (∏ i, gap r i)^4 = vFive (fun i => r i.castSucc) := by
  rw [← five_edge_units]
  unfold vFive
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  split_ifs with h
  · have hi := sub_ne_zero.mpr (hr.ne (Fin.castSucc_ne_last i))
    have hj := sub_ne_zero.mpr (hr.ne (Fin.castSucc_ne_last j))
    change ((r i.castSucc-r (Fin.last 5))⁻¹-(r j.castSucc-r (Fin.last 5))⁻¹)*
      -((r i.castSucc-r (Fin.last 5))*(r j.castSucc-r (Fin.last 5))) = _
    rw [sub_mul, mul_neg, mul_neg, ← mul_assoc, inv_mul_cancel₀ hi,one_mul,
      mul_comm (r i.castSucc-r (Fin.last 5)),← mul_assoc,inv_mul_cancel₀ hj,one_mul]
    ring
  · ring

/-- For the actual rational sextic and its restricted quintic,
the change of discriminant is exactly the twentieth power of the ordinate scale. -/
theorem sextic_discriminant (f : ℚ[X]) (hd : f.natDegree=6) (r : Fin 6 → ℂ)
    (hr : Function.Injective r) (hz : ∀ i, aeval (r i) f = 0) (s : ℂ)
    (hs : s^2 = ordinateFactor (f.leadingCoeff : ℂ) r) :
    (quintic r).discr * s^20 = (f.discr : ℂ) := by
  have factors : (∏ i : Fin 5, (r (Fin.last 5)-r i.castSucc)) = -(∏ i, gap r i) := by
    calc
      _ = ∏ i, (-1:ℂ)*gap r i := Finset.prod_congr rfl (fun i _ => by dsimp [gap]; ring)
      _ = _ := by rw [Finset.prod_mul_distrib]; norm_num
  have scale : s^2 = -((f.leadingCoeff : ℂ)*(∏ i, gap r i)) := by
    rw [hs,ordinateFactor,factors,mul_neg]
  rw [quintic_discriminant,discriminant_roots _ hd _ hr hz,six_edges,← inverse_edges r hr]
  calc
    _ = (vFive (finiteBranches r))^2 * (s^2)^10 := by ring
    _ = _ := by rw [scale]; ring

end
end ZInQBlueprint.ArchimedeanHeight
#print axioms ZInQBlueprint.ArchimedeanHeight.sextic_discriminant
