import InertWords

namespace Sun28.CommonRows
open Finset Sun28.MixedSieve Sun28.PrimeLower
open private circle_size from InertWords
open scoped Classical
noncomputable section
variable {p:ℕ} [Fact p.Prime] {ι:Type*} [Fintype ι] [DecidableEq ι]

/-- Second finite difference of the power function. The proof works also with zero or one position. -/
theorem power_difference (x:ℝ) (hx:1≤x) (k:ℕ) :
    ((x+1)^k-2*x^k+(x-1)^k)*(x+1)^2≤(k:ℝ)*(k-1)*(x+1)^k := by
  have xl : 0≤x+1 := by linarith
  have xu : 0≤x-1 := by linarith
  have first (n:ℕ) : (x+1)*(x^n-(x-1)^n) ≤ (n:ℝ)*(x+1)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have pwr:=pow_le_pow_left₀ (show 0≤x by linarith) (show x≤x+1 by linarith) n
      have inc:=mul_le_mul_of_nonneg_left ih xu
      have add:=mul_le_mul_of_nonneg_left pwr xl
      have npos : 0≤(n:ℝ)*(x+1)^n := by positivity
      rw [Nat.cast_succ,pow_succ,pow_succ,pow_succ];nlinarith only [inc,add,npos]
  induction k with
  | zero => norm_num
  | succ n ih =>
    have scale:=mul_le_mul_of_nonneg_left ih xl
    have diff:=mul_le_mul_of_nonneg_left (first n) xl
    rw [Nat.cast_succ,pow_succ,pow_succ,pow_succ];nlinarith only [scale,diff]

/-- Exact probability lost in the actual Gaussian norm fibres over independent
ordinary residues. The hypothesis of distinct coefficients is local modulo p. -/
theorem exact_inert_average (c:ι→ZMod p) (inert:p%4=3) (inj:Function.Injective c) :
    averageLoss c = (((p:ℝ)+1)^(Fintype.card ι)-2*(p:ℝ)^(Fintype.card ι)+
      ((p:ℝ)-1)^(Fintype.card ι))/(((p:ℝ)+1)^(Fintype.card ι))/(p:ℝ)^2 := by
  classical
  let s:=(obstructed (p:=p) (fun _:ι=>(1:ZMod p)))
  let k:=Fintype.card ι
  have cp:=circle_size inert
  have nt : Fintype.card (ι→Circle p 1)=(p+1)^k := by simp [cp,k]
  have complement:=inert_safe_count inert ι
  have cardSum:=Finset.card_compl_add_card s
  have tally : (s.card:ℝ)=((p:ℝ)+1)^k-2*(p:ℝ)^k+((p:ℝ)-1)^k := by
    rw [nt] at cardSum
    have hy : (sᶜ.card:ℤ)=2*(p:ℤ)^k-((p-1:ℕ):ℤ)^k:=complement
    have castSum:(sᶜ.card:ℝ)+(s.card:ℝ)=((p:ℝ)+1)^k := by exact_mod_cast cardSum
    have castComp:(sᶜ.card:ℝ)=2*(p:ℝ)^k-((p-1:ℕ):ℝ)^k:=by exact_mod_cast hy
    rw [Nat.cast_sub (by omega:1≤p),Nat.cast_one] at castComp
    linarith
  have support (w u:ZMod p) : loss c u w =
      (if w=0 then (if u=1 then ((s.card:ℝ)/((p:ℝ)+1)^k) else 0) else 0) := by
    by_cases both:u=1∧w=0
    · obtain ⟨rfl,rfl⟩:=both
      let mass (t:ι→ZMod p):ℝ := if ∀ i,t i≠0 then
        ((obstructed t).card:ℝ)/Fintype.card ((i:ι)→Circle p (t i)) else 0
      change mass (norms c 1 0)=_
      rw [show norms c 1 0=(fun _=>1) by funext i;simp [norms]]
      simp [mass,s,cp,k]
    · have empty:obstructed (norms c u w)=∅:=by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hit;exact both (inert_collision inert inj z hit)
      by_cases hw:w=0
      · have hu:u≠1:=fun hu=>both ⟨hu,hw⟩
        simp [loss,empty,hw,hu]
      · simp [loss,empty,hw]
  unfold averageLoss
  simp_rw [support]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [tally]

theorem inert_average_bound (c:ι→ZMod p) (inert:p%4=3) (inj:Function.Injective c) :
    averageLoss c ≤ (Fintype.card ι:ℝ)*(Fintype.card ι-1)/(((p:ℝ)+1)^2*(p:ℝ)^2) := by
  rw [exact_inert_average c inert inj]
  have hp : (1:ℝ)≤p:=by exact_mod_cast (Fact.out:p.Prime).one_le
  have pos : 0<(p:ℝ)+1:=by linarith
  rw [←div_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  rw [div_le_div_iff₀ (pow_pos pos _) (sq_pos_of_pos pos)]
  exact power_difference _ hp _

end
end Sun28.CommonRows
#print axioms Sun28.CommonRows.power_difference
#print axioms Sun28.CommonRows.exact_inert_average
#print axioms Sun28.CommonRows.inert_average_bound
