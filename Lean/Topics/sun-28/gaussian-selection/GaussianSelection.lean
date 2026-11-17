import GaussianOrders
import ShiftTuple

namespace Sun28.GaussianSelection
open ManuscriptV15.Arithmetic Sun28.ContactFactors Sun28.Ordinary

/-- Each rational shift retains its own Gaussian generator and both ray conditions. -/
structure OrientedAt (A : Fin 3→ℚ) {u v : ℕ} (h : PrimeValues A u v)
    (π : ↥(shifts A)→Gaussian) (M : ℕ) : Prop where
  norm : ∀ r,gaussianPrime (π r) ∧ gaussianNorm (π r) = h.value r
  ray16 : ∀ r,gaussianCongruent 16 (π r) (9,0)
  ray7 : ∀ r,gaussianCongruent 7 (π r) (1,3)
  rayM : ∀ r,gaussianCongruent M (π r) (0,1)
  cross : ∀ r s,(adjacentNorm (π r) false).gcd (adjacentNorm (π s) true)=4
  avoid : ∀ r e,(adjacentNorm (π r) e).Coprime (7*M)

private theorem oriented_tuple (gauss : GaussianTuples) (A : Fin 3→ℚ) (one : A 0=1)
    (d M : ℕ) (dp : 0<d) (mp : 0<M) (mo : Odd M) (ms : squarefree M) (m7 : ¬7∣M)
    (H Y : ℝ) : ∃ (u v : ℕ) (h : PrimeValues A u v) (π : ↥(shifts A)→Gaussian),
      0<u ∧ 0<v ∧ d∣v ∧ H<(slope A u v:ℝ) ∧
      (∀ r∈shifts A,primeSize A Y<(h.value r:ℝ)) ∧ OrientedAt A h π M := by
  classical
  let S:=shifts A
  let t:=S.equivFin
  let c (i : Fin S.card) := offset (dilation A) (t.symm i)
  have inj : Function.Injective c := by
    intro i j eq
    exact t.symm.injective (Subtype.ext (offset_injective (t.symm i).property (t.symm j).property eq))
  have enough : 2≤S.card := by change 2≤(shifts A).card; have := enough_shifts A one; omega
  let D : ℝ := dilation A
  have D0 : 0<D := by dsimp [D]; exact_mod_cast dilation_positive A
  obtain ⟨u,v,up,vp,lower,p,pat,large⟩:=
    gauss S.card enough c inj d M dp mp mo ms m7 ((|H|+1)*D^2) (primeSize A Y)
      (by positivity) (size_bounds A Y).1
  obtain ⟨div,z,vals,_,_,_,cross,avoid⟩:=pat
  let h : PrimeValues A u v := {
    value:=fun r=>if hr : r∈S then p (t ⟨r,hr⟩) else 0
    prime:=by intro r hr; change r∈S at hr; simpa only [dite_eq_left hr] using (vals (t ⟨r,hr⟩)).2.1
    equation:=by intro r hr; change r∈S at hr; simp only [dite_eq_left hr]; simpa [c] using (vals (t ⟨r,hr⟩)).1 }
  let π (r : ↥S) := z (t r)
  have val_eq (r : ↥S) : h.value r=p (t r) := by simp [h,r.property]
  have slope_eq : (slope A u v:ℝ)=(u:ℝ)/(D*v)^2 := by
    simp [Sun28.ContactFactors.slope,D]
  have big : H<(slope A u v:ℝ) := by
    rw [slope_eq,mul_pow,lt_div_iff₀ (by positivity)]
    have v0 : (0:ℝ)<v := by exact_mod_cast vp
    have pre:= (lt_div_iff₀ (by positivity : (0:ℝ)<(v:ℝ)^2)).mp lower
    have hle : H*D^2≤(|H|+1)*D^2 := mul_le_mul_of_nonneg_right (by linarith [le_abs_self H]) (sq_nonneg D)
    exact (by simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hle (sq_nonneg (v:ℝ))).trans_lt pre)
  refine ⟨u,v,h,π,up,vp,div,big,?_,?_⟩
  · intro r hr
    rw [show h.value r=p (t ⟨r,hr⟩) from val_eq ⟨r,hr⟩]
    exact large _
  · exact {
      norm:=fun r=>⟨(vals (t r)).2.2.1,(vals (t r)).2.2.2.1 |>.trans (val_eq r).symm⟩
      ray16:=fun r=>(vals (t r)).2.2.2.2.1
      ray7:=fun r=>(vals (t r)).2.2.2.2.2.1
      rayM:=fun r=>(vals (t r)).2.2.2.2.2.2
      cross:=fun r s=>cross (t r) (t s)
      avoid:=fun r e=>avoid (t r) e }

/-- The simultaneous prime theorem at the merged shifts, with prescribed dilation,
lower bounds and local input fixed before either parameter is chosen. -/
theorem select_with_orders (gauss : GaussianTuples) (A : Fin 3→ℚ) (one : A 0=1) (alive : ∀ j,A j≠0)
    (d κ : ℕ) (T : Finset ℕ) (a : ℕ→ℕ) (dp : 0<d) (κp : 0<κ)
    (primes : ∀ p∈T,p.Prime) (two : 2∈T) (depth : ∀ p∈T,padicValNat p κ≤a p) (a2 : 6≤a 2)
    (H Y : ℝ) :
    ∃ (u v : ℕ) (h : PrimeValues A u v) (π : ↥(shifts A)→Gaussian) (o : Orders),
      0<u ∧ 0<v ∧ d∣v ∧ H<(slope A u v:ℝ) ∧ (∀ r∈shifts A,Y<(h.value r:ℝ)) ∧
      (∀ j,∀ p∈selected h j,¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0) ∧
      OrientedAt A h π (avoidModulus T κ) ∧
      o.plusOrder=orderLcm π true ∧ o.minusOrder=orderLcm π false ∧
      o.kernelModulus=κ ∧ o.T=T ∧ o.a=a := by
  classical
  let M:=avoidModulus T κ
  obtain ⟨mp,mo,ms,m7,_⟩:=avoid_modulus_spec T κ primes
  obtain ⟨u,v,h,π,up,vp,div,big,large,oriented⟩:=
    oriented_tuple gauss A one d M dp mp mo ms m7 H Y
  let localNonempty : Nonempty ↥(shifts A) :=
    ⟨⟨-0/A 0,shift_mem A 0 (by norm_num [marks])⟩⟩
  obtain ⟨o,lp,lm,ko,ts,ao⟩:=
    orders_of_generators π κ T a κp primes two depth a2 oriented.ray16 oriented.cross oriented.avoid
  have good (r : ℚ) (hr : r∈shifts A) :=
    large_prime_exclusions A Y alive (large r hr)
  refine ⟨u,v,h,π,o,up,vp,div,big,fun r hr=>(good r hr).1,?_,oriented,lp,lm,ko,ts,ao⟩
  intro j p hp
  obtain ⟨θ,hθ,rfl⟩:=Finset.mem_image.mp hp
  have vgood := (good (-θ/A j) (shift_mem A j hθ)).2
  exact ⟨vgood.1,vgood.2.1,vgood.2.2 j⟩

end Sun28.GaussianSelection
#print axioms Sun28.GaussianSelection.select_with_orders
