import PrimeOccurrences

namespace Sun28.ContactFactors
open Sun28.Ordinary
noncomputable section
variable {A : Fin 3→ℚ} {u v : ℕ}

def selected (h : PrimeValues A u v) (j : Fin 3) : Finset ℕ :=
  marks.image fun a => h.value (-a/A j)

def argument (A : Fin 3→ℚ) (u v : ℕ) (j : Fin 3) : ℚ :=
  A j*u/((dilation A*v:ℕ):ℚ)^2

def scaleFactor (w : ℕ) (t : ℚ) : ℚ := 1/((w:ℚ)^5*(t-3)^3)

private theorem contact_eq (h : PrimeValues A u v) (vp : 0<v) (j : Fin 3) (nz : A j≠0)
    {a : ℚ} (ha : a∈marks) :
    argument A u v j-a=(A j/((dilation A*v:ℕ):ℚ)^2)*(h.value (-a/A j):ℚ) := by
  rw [h.rational_equation (shift_mem A j ha)]
  unfold argument
  have wn : ((dilation A*v:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos (dilation_positive A) vp).ne'
  field_simp [nz,wn]
  ring

theorem selected_prime (h : PrimeValues A u v) {p : ℕ} {j : Fin 3} (hp : p∈selected h j) :
    p.Prime := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
  exact h.prime _ (shift_mem A j ha)

theorem detector_factorization (h : PrimeValues A u v) (vp : 0<v) (j : Fin 3) (nz : A j≠0) :
    detector (A j) (argument A u v j) =
      scaleFactor (dilation A*v) (argument A u v j)^2 * ∏ p ∈ selected h j, (p:ℚ) := by
  have inj : Set.InjOn (fun a : ℚ => h.value (-a/A j)) (↑marks) := by
    intro a ha b hb eqn
    have e:=h.injective_on vp (shift_mem A j ha) (shift_mem A j hb) eqn
    exact neg_injective ((div_left_inj' nz).mp e)
  have product : (∏ p ∈ selected h j, (p:ℚ)) = ∏ a∈marks, (h.value (-a/A j):ℚ) :=
    Finset.prod_image (fun a ha b hb e => inj ha hb e)
  have card : marks.card=5 := by norm_num [marks, Finset.card_insert_of_notMem]
  have fac : fiveProduct (argument A u v j) =
      (A j/((dilation A*v:ℕ):ℚ)^2)^5 * ∏ p ∈ selected h j, (p:ℚ) := by
    unfold fiveProduct
    rw [product,← card,← Finset.prod_const,← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun a ha => contact_eq h vp j nz ha)
  unfold detector scaleFactor
  rw [fac]
  by_cases guard : argument A u v j-3=0
  · simp [guard]
  have wn : ((dilation A*v:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos (dilation_positive A) vp).ne'
  field_simp [nz,wn,guard]

theorem selected_unit (h : PrimeValues A u v) (one : A 0=1) (vp : 0<v) {j : Fin 3} (nz : A j≠0)
    {p : ℕ} (hp : p∈selected h j) (off : ¬p∣dilation A) (good : ¬p∣separation) (unit : padicValRat p (A j)=0) :
    argument A u v j≠3 ∧
    padicValRat p (scaleFactor (dilation A*v) (argument A u v j))=0 := by
  obtain ⟨a,ha,eqn⟩ := Finset.mem_image.mp hp
  let _ := Fact.mk (selected_prime h hp)
  have wn : ((dilation A*v:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos (dilation_positive A) vp).ne'
  have nd : ¬p∣dilation A*v := eqn ▸ h.unit_at_denominator one vp (shift_mem A j ha) (eqn ▸ off)
  have wunit : padicValRat p ((dilation A*v:ℕ):ℚ)=0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd nd];rfl
  have pp : p.Prime := selected_prime h hp
  have npr : (p:ℚ)≠0 := by exact_mod_cast pp.ne_zero
  have e := contact_eq h vp j nz ha
  rw [eqn] at e
  have depth : padicValRat p (argument A u v j-a)=1 := by
    rw [e,padicValRat.mul (div_ne_zero nz (pow_ne_zero 2 wn)) npr,
      padicValRat.div nz (pow_ne_zero 2 wn),padicValRat.pow,unit,wunit,padicValRat.self pp.one_lt]
    norm_num
  have a3 : a≠3 := fun e => (by norm_num [marks] : (3:ℚ)∉marks) (e ▸ ha)
  have guard : argument A u v j≠3 := by
    intro eq
    rw [eq,mark_difference_unit good (Finset.mem_insert_self ..) (Finset.mem_insert_of_mem ha) a3.symm] at depth
    contradiction
  have loc :=  other_marks_unit good ha (Finset.mem_insert_self ..) a3 guard (show 0<padicValRat p (argument A u v j-a) by omega)
  refine ⟨guard,?_⟩
  unfold scaleFactor
  rw [padicValRat.div one_ne_zero (mul_ne_zero (pow_ne_zero 5 wn) (pow_ne_zero 3 (sub_ne_zero.mpr guard))),
    padicValRat.mul (pow_ne_zero 5 wn) (pow_ne_zero 3 (sub_ne_zero.mpr guard)),padicValRat.pow,padicValRat.pow,
    wunit,loc]
  simp

end
end Sun28.ContactFactors
#print axioms Sun28.ContactFactors.selected_prime
#print axioms Sun28.ContactFactors.detector_factorization
#print axioms Sun28.ContactFactors.selected_unit
