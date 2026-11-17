import HPSmallPrimes

/-! Exceptional absolute invariants and their normalized HP coefficients. -/
namespace ZInQBlueprint.JacobianHeight.ExactFinite
open ZInQ SixContactHP
noncomputable section

private theorem integral_int (p : ℕ) (a : ℤ) : 0 ≤ padicValRat p (a:ℚ) := by
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

private theorem integral_add {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y) : 0 ≤ padicValRat p (x+y) := by
  by_cases hv : x+y=0
  · simp [hv]
  exact (le_min hx hy).trans (padicValRat.min_le_padicValRat_add hv)

private theorem integral_mul {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y) : 0 ≤ padicValRat p (x*y) := by
  by_cases x0 : x=0
  · simp [x0]
  by_cases y0 : y=0
  · simp [y0]
  rw [padicValRat.mul x0 y0]
  exact add_nonneg hx hy

private def horner (j : ℚ) : List ℤ → ℚ
  | [] => 0
  | c::cs => (c:ℚ)+j*horner j cs

private theorem horner_integral {p : ℕ} [Fact p.Prime] {j : ℚ}
    (hj : 0 ≤ padicValRat p j) (cs : List ℤ) : 0 ≤ padicValRat p (horner j cs) := by
  induction cs with
  | nil => simp [horner]
  | cons c cs ih => exact integral_add (integral_int p c) (integral_mul hj ih)

private theorem unit_horner {p : ℕ} [Fact p.Prime] {j : ℚ} (hj : 0 < padicValRat p j)
    (c : ℤ) (hc : ¬(p:ℤ) ∣ c) (cs : List ℤ) :
    horner j (c::cs) ≠ 0 ∧ padicValRat p (horner j (c::cs)) = 0 := by
  have c0 : (c:ℚ) ≠ 0 := by
    exact_mod_cast (show c ≠ 0 by rintro rfl; exact hc (dvd_zero _))
  have cv : padicValRat p (c:ℚ)=0 := by
    have nd : ¬p ∣ c.natAbs := fun d => hc (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr d))
    rw [padicValRat.of_int]
    change (padicValNat p c.natAbs : ℤ)=0
    rw [padicValNat.eq_zero_of_not_dvd nd]
    rfl
  change ((c:ℚ)+j*horner j cs ≠ 0) ∧ _
  simp only [horner] at ⊢
  by_cases e : j*horner j cs=0
  · simp [e,c0,cv]
  have j0 : j ≠ 0 := by rintro rfl; simp at hj
  have h0 : horner j cs ≠ 0 := fun h => e (by simp [h])
  have high : 0 < padicValRat p (j*horner j cs) := by
    rw [padicValRat.mul j0 h0]
    exact add_pos_of_pos_of_nonneg hj (horner_integral hj.le cs)
  have nz : (c:ℚ)+j*horner j cs ≠ 0 := by
    intro eq
    have h : j*horner j cs = -(c:ℚ) := by linarith
    rw [h,padicValRat.neg,cv] at high
    omega
  exact ⟨nz,(padicValRat.add_eq_of_lt nz c0 e (by omega)).trans cv⟩

/-- For residue characteristics 2 and 3 the upper absolute invariants are units on the paper chart. -/
theorem exceptional_units {u : ℚ} (hu : u ∉ contactSet) :
    (j8 (SixContact.J u) ≠ 0 ∧ padicValRat 2 (j8 (SixContact.J u))=0) ∧
    (j6 (SixContact.J u) ≠ 0 ∧ padicValRat 3 (j6 (SixContact.J u))=0) := by
  let j := SixContact.J u
  have h8 : j8 j = horner j [3,-6,-51,-30,3] := by
    simp only [horner,j8,j6]; push_cast; ring
  have h6 : j6 j = horner j [4,0,-8,4] := by
    simp only [horner,j6]; push_cast; ring
  change (j8 j ≠ 0 ∧ _) ∧ (j6 j ≠ 0 ∧ _)
  change (j8 j ≠ 0 ∧ padicValRat 2 (j8 j)=0) ∧ (j6 j ≠ 0 ∧ padicValRat 3 (j6 j)=0)
  rw [h8,h6]
  exact ⟨unit_horner (small_orders hu).1 3 (by decide) _,unit_horner (small_orders hu).2 4 (by decide) _⟩

/-- Explicit signed orders before dividing by the local weight 4 or 3. -/
theorem exceptional_orders {u : ℚ} (hu : u ∉ contactSet) :
    padicValRat 2 (inverseLocalInvariant u 2)=12*padicValRat 2 (SixContact.J u) ∧
    padicValRat 3 (inverseLocalInvariant u 3)=9*padicValRat 3 (SixContact.J u) := by
  have hj := (CoarseConic.unmarked_range hu).2.ne
  obtain ⟨⟨n8,v8⟩,⟨n6,v6⟩⟩ := exceptional_units hu
  constructor
  · simp only [inverseLocalInvariant,↓reduceIte]
    rw [padicValRat.div (pow_ne_zero _ (pow_ne_zero _ hj)) (pow_ne_zero _ n8),
      padicValRat.pow,padicValRat.pow,padicValRat.pow,v8]
    push_cast
    ring
  · simp only [inverseLocalInvariant,show (3:ℕ) ≠ 2 by decide,↓reduceIte]
    rw [padicValRat.div (pow_ne_zero _ (pow_ne_zero _ hj)) (pow_ne_zero _ n6),
      padicValRat.pow,padicValRat.pow,padicValRat.pow,v6]
    push_cast
    ring

/-- The published normalized finite summand above each prime, including 2 and 3. -/
theorem finiteTerm_all_primes (K : Type) [Field K] [NumberField K] {u : ℚ}
    (hu : u ∉ contactSet) {p : ℕ} (hp : p.Prime) :
    finiteTerm K u p = (Module.finrank ℚ K : ℝ) *
      (((3*max 0 (padicValRat p (SixContact.J u))+2*max 0 (-padicValRat p (SixContact.J u)):ℤ):ℝ) *
        Real.log p) := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [finiteTerm,degreeSum_eq K hp]
  congr 1
  congr 1
  norm_num only [Int.cast_zero]
  change (max (0:ℝ) (padicValRat p (inverseLocalInvariant u p) : ℝ)) /
    ((if p=2 then 4 else if p=3 then 3 else 1 : ℕ):ℝ) = _
  by_cases p2 : p=2
  · subst p
    rw [(exceptional_orders hu).1]
    have v := (small_orders hu).1
    norm_num
    rw [max_eq_right (by positivity : (0:ℝ) ≤ 12*(padicValRat 2 (SixContact.J u):ℝ)),
      max_eq_right (by positivity : (0:ℝ) ≤ (padicValRat 2 (SixContact.J u):ℝ)),
      max_eq_left (by exact_mod_cast (show -(padicValRat 2 (SixContact.J u)) ≤ 0 by omega))]
    ring
  by_cases p3 : p=3
  · subst p
    rw [(exceptional_orders hu).2]
    have v := (small_orders hu).2
    norm_num
    rw [max_eq_right (by positivity : (0:ℝ) ≤ 9*(padicValRat 3 (SixContact.J u):ℝ)),
      max_eq_right (by positivity : (0:ℝ) ≤ (padicValRat 3 (SixContact.J u):ℝ)),
      max_eq_left (by exact_mod_cast (show -(padicValRat 3 (SixContact.J u)) ≤ 0 by omega))]
    ring
  have large : 3 < p := by have := hp.two_le; omega
  have nz := (CoarseConic.unmarked_range hu).2.ne
  have succ : SixContact.J u+1 ≠ 0 := by linarith [(CoarseConic.unmarked_range hu).1]
  simp only [inverseLocalInvariant,p2,p3,↓reduceIte,Nat.cast_one,div_one]
  exact_mod_cast tame_order large nz succ

end
end ZInQBlueprint.JacobianHeight.ExactFinite
#print axioms ZInQBlueprint.JacobianHeight.ExactFinite.exceptional_units
#print axioms ZInQBlueprint.JacobianHeight.ExactFinite.exceptional_orders
#print axioms ZInQBlueprint.JacobianHeight.ExactFinite.finiteTerm_all_primes
