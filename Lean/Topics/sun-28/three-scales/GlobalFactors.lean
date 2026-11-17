import FiniteFactors
import ScaleHeights

namespace Sun28.Ordinary
open ZInQ ZInQ.Mult NumberField Height
open scoped NumberField
noncomputable section

private theorem finite_max_factor (w : FinitePlace K0) (m : Fin 4 → ℤ) (odd : ∀ j, Odd (m j)) (i : Fin 4) :
    max (w (indexX (m i))) 1 ≤ max (w (coordinateProduct m)) 1 * max (w (delta⁻¹^6)) 1 := by
  classical
  by_cases pole : 1 < w (indexX (m i))
  · rw [max_eq_left pole.le]
    let xs := fun j => w (indexX (m j))
    have bounds (j : Fin 4) : w delta^2 ≤ xs j :=
      finite_pole_companion w (odd i) (by have ⟨k,h⟩:=odd j; omega) pole
    have cmp := Finset.prod_le_prod₀ (s:=Finset.univ.erase i)
      (f:=fun _ : Fin 4 => w delta^2) (g:=xs) (fun _ _ => sq_nonneg _) (fun j _ => bounds j)
    have card : (Finset.univ.erase i).card=3 := by simp
    rw [Finset.prod_const,card,←pow_mul] at cmp
    have prod := mul_le_mul_of_nonneg_left cmp (apply_nonneg w (indexX (m i)))
    change xs i * (w delta)^(2*3) ≤ xs i * _ at prod
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at prod
    have d : w delta ≠ 0 := by simpa using delta_ne_zero
    have mult : xs i ≤ w (coordinateProduct m) * w (delta⁻¹^6) := by
      rw [coordinateProduct,map_prod,map_pow,map_inv₀,inv_pow,←div_eq_mul_inv,le_div_iff₀ (pow_pos (lt_of_le_of_ne (apply_nonneg w delta) d.symm) 6)]
      exact prod
    exact mult.trans (mul_le_mul (le_max_left _ _) (le_max_left _ _) (apply_nonneg w _) (le_trans (apply_nonneg w _) (le_max_left _ _)))
  · rw [max_eq_right (le_of_not_gt pole)]
    exact one_le_mul_of_one_le_of_one_le (le_max_right _ _) (le_max_right _ _)

private theorem arch_max_factor (w : InfinitePlace K0) (m : Fin 4 → ℤ) (odd : ∀ j, Odd (m j)) (i : Fin 4) :
    max (w (indexX (m i))) 1 ≤ max (w (coordinateProduct m)) 1 := by
  classical
  have pos (j : Fin 4) : 1 ≤ w (indexX (m j)) := all_infinite_abscissas (by have ⟨t,h⟩:=odd j; omega) w
  rw [max_eq_left (pos i),coordinateProduct,map_prod]
  apply le_trans _ (le_max_left _ _)
  rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (apply_nonneg w _) (Finset.one_le_prod₀ (fun j _=> pos j))

private theorem global_domination {x c e : K0} (xn : x≠0) (cn : c≠0) (en : e≠0)
    (infinite : ∀ w : InfinitePlace K0, max (w x) 1 ≤ max (w c) 1)
    (finite : ∀ w : FinitePlace K0, max (w x) 1 ≤ max (w c) 1 * max (w e) 1) :
    hK0 x ≤ hK0 c + hK0 e := by
  classical
  let A := fun z : K0 => ∏ w : InfinitePlace K0, max (w z) 1 ^w.mult
  let F := fun z : K0 => ∏ᶠ w : FinitePlace K0, max (w z) 1
  have arch : A x ≤ A c := Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun w _ => pow_le_pow_left₀ (by positivity) (infinite w) _)
  have a1 : 1 ≤ A e := Finset.one_le_prod₀ (fun w _ => one_le_pow₀ (le_max_right _ _))
  have fs (z : K0) (nz : z≠0) : (fun w : FinitePlace K0 => max (w z) 1).HasFiniteMulSupport := by
    apply (FinitePlace.hasFiniteMulSupport (K:=K0) nz).subset
    intro w hw
    contrapose! hw
    simp only [Function.mem_mulSupport,not_ne_iff] at hw
    simp [Function.mem_mulSupport,hw]
  have fin : F x ≤ F c * F e := by
    unfold F
    rw [←finprod_mul_distrib (fs c cn) (fs e en)]
    exact finprod_le_finprod₀ (fs x xn) (fun w => (zero_le_one.trans (le_max_right _ _))) ((fs c cn).mul (fs e en)) finite
  have anon (z:K0) : 0 ≤ A z := Finset.prod_nonneg (fun _ _ => by positivity)
  have fnon (z:K0) : 0 ≤ F z := finprod_nonneg (fun _ => zero_le_one.trans (le_max_right _ _))
  have h : mulHeight₁ x ≤ mulHeight₁ c * mulHeight₁ e := by
    rw [NumberField.mulHeight₁_eq,NumberField.mulHeight₁_eq,NumberField.mulHeight₁_eq]
    change A x*F x ≤ (A c*F c)*(A e*F e)
    calc A x*F x ≤ A c*(F c*F e) := mul_le_mul arch fin (fnon x) (anon c)
      _ ≤ (A c*(F c*F e))*A e := le_mul_of_one_le_right (mul_nonneg (anon c) (mul_nonneg (fnon c) (fnon e))) a1
      _ = _ := by ring
  have hlog := Real.log_le_log (mulHeight₁_pos x) h
  rw [Real.log_mul (mulHeight₁_pos c).ne' (mulHeight₁_pos e).ne'] at hlog
  simp only [hK0,logHeight₁_eq_log_mulHeight₁]
  linarith

/-- The possible finite cancellation costs at most three times log 7, independently of the odd indices. -/
theorem abscissa_product_bound (m : Fin 4 → ℤ) (odd : ∀ j, Odd (m j)) (i : Fin 4) :
    hK0 (indexX (m i)) ≤ hK0 (coordinateProduct m) + 3 * Real.log 7 := by
  have nz (j : Fin 4) : indexX (m j) ≠ 0 := indexX_nonzero (by obtain ⟨l,e⟩:=odd j; omega)
  have c : coordinateProduct m ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _=> nz j)
  have h := global_domination (nz i) c (pow_ne_zero 6 (inv_ne_zero delta_ne_zero))
    (fun w => arch_max_factor w m odd i) (fun w => finite_max_factor w m odd i)
  have inv : hK0 delta⁻¹ = hK0 delta := by simp [hK0,logHeight₁_inv]
  rw [hK0_pow,inv,hK0_delta] at h
  norm_num at h ⊢
  linarith

end
end Sun28.Ordinary
#print axioms Sun28.Ordinary.abscissa_product_bound
