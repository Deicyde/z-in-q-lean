import DyadicCount
import CongruenceProjection

namespace Sun28.ConeCount
open Finset Filter Topology Sun28.ConeSieve Sun28.QuadricSieve Sun28.ConeFibres Sun28.ConeEuler
open Sun28.ContactFactors Sun28.WeightedSelection Sun28.SieveTail Sun28.SinglePrime Sun28.MediumSieve
open scoped Classical
noncomputable section

/-- The unrestricted coefficient is chosen before the row width. The constant
in the error may depend on that width. -/
theorem row_data (input : PublishedQuadricCount) {A : Fin 3→ℚ} (pair : ↥(shifts A)×↥(shifts A)) :
    ∃ H : ℝ,0≤H ∧ ∀ j : ℕ,∃ D : ℝ,0≤D ∧ (pair.1≠pair.2 →
      ∃ (σ : ℝ) (ρ : ℕ→ℝ),0≤σ ∧ σ≤ConeReal.rowConstant*ConeReal.width j ∧
        Estimate (gap pair.1 pair.2) 2 (ConeReal.weight j) (H*σ) D ρ) := by
  by_cases eq : pair.1=pair.2
  · exact ⟨0,le_rfl,fun _=>⟨0,le_rfl,fun diff=>(diff eq).elim⟩⟩
  obtain ⟨H,ρ,hn,_,weights⟩:=input (gap pair.1 pair.2) (gap_ne_zero eq)
  refine ⟨H,hn,?_⟩
  intro j
  obtain ⟨σ,sn,limit,D,dn,est⟩:=weights 2 (ConeReal.weight j) (ConeReal.smooth_weight j)
    (ConeReal.compact_weight j) (fun x=>(ConeReal.weight_bounds j x).1)
    (fun _ h=>by simpa using ConeReal.support_norm j h) (fun _ h=>ConeReal.regular_support _ j h)
  exact ⟨D,dn,fun _=>⟨σ,ρ,sn,ConeReal.density_le _ j limit,est⟩⟩

def UniformProducts (A : Fin 3→ℚ) : Prop :=
  ∃ c : ℝ,0<c ∧ ∀ᶠ t : ℕ in atTop,∀ (p : ℕ) (g : ℕ→ℝ),
    LocalApproximation (threshold A) (shifts A).card 50 g →
    let P:=auxPrimes (threshold A) (smallLevel t) p
    (∀ q∈P,q.Prime ∧ q≠p ∧ q≤level t ∧ 0≤g q ∧ g q<1 ∧ 1+2*odds g q≤q) ∧
    (2*∑ q∈P,g q*Real.log q≤Real.log (level t)) ∧
    c*(growthBound A t:ℝ)^(shifts A).card≤∏ q∈P,(1+odds g q)

theorem products_from_mertens (mertens : PublishedMertensFour) (A : Fin 3→ℚ) (one : A 0=1) :
    UniformProducts A := by
  have base : 64≤threshold A:=le_max_left ..
  have cap : (50:ℝ)≤(threshold A:ℝ) := by exact_mod_cast (show 50≤threshold A by omega)
  exact sieve_primes mertens A base cap (by norm_num) (by have h:=enough_shifts A one;omega)
    (Sun28.GaussianSelection.shifts_card_le A)

theorem congruences (quadric : PublishedQuadricCount)
    (products : ∀ A : Fin 3→ℚ,A 0=1→UniformProducts A) : CongruenceInputs := by
  classical
  intro X b v n _
  let A:=Sun28.RealPoleBounds.fixedScale n
  have one : A 0=1 := by simp [A,Sun28.RealPoleBounds.fixedScale,Sun28.Ordinary.scaleRoot]
  obtain ⟨c,cp,sieve⟩:=products A one
  let I:=↥(shifts A)×↥(shifts A)
  choose H non rows using row_data (A:=A) quadric
  let Z:=∑ a : I,H a
  have hn (a : I) : H a≤Z:=single_le_sum (fun k _=>non k) (mem_univ a)
  have zn : 0≤Z:=sum_nonneg (fun a _=>non a)
  have rn : 0≤ConeReal.rowConstant:=by unfold ConeReal.rowConstant;positivity
  refine ⟨threshold A,8*(maxCoefficient A+1),64*Z*ConeReal.rowConstant/c,by positivity,?_⟩
  intro j high
  choose D dn data using fun a : I=>rows a j
  let U:=∑ a : I,D a
  have du (a : I) : D a≤U:=single_le_sum (fun k _=>dn k) (mem_univ a)
  have un : 0≤U:=sum_nonneg (fun a _=>dn a)
  refine ⟨2*((j:ℝ)+1)*U,by positivity,?_⟩
  filter_upwards [sieve,cutoff_level A,log_scale (j:=j)] with t all cut wide
  intro p large below pr
  let _ : Fact p.Prime:=⟨pr⟩
  intro i k diff
  let a : I:=(i,k)
  obtain ⟨σ,ρ,sn,sb,est⟩:=data a diff
  have ha:=non a
  have da:=dn a
  have narrow : 8*(maxCoefficient A+1)≤j+1:=by omega
  let P:=auxPrimes (threshold A) (smallLevel t) p
  let g:=density i k
  obtain ⟨primes,mean,prod⟩:=all p g (flag_approximation i k diff)
  let L:=factor localWeight p (residues p (gap i k))
  obtain ⟨lp,lb⟩:=collision_bound (κ:=gap i k) (good_gap diff pr large).2.1
  have pp : (0:ℝ)<p:=by exact_mod_cast pr.pos
  have gb : (0:ℝ)<growthBound A t:=by unfold growthBound;positivity
  have side' : 0≤(side t:ℝ):=Nat.cast_nonneg _
  refine ⟨ConeReal.majorant j t p i k narrow,P,g,H a*σ*(side t:ℝ)^3*L,
    U*(2:ℝ)^(559*t),primes,by positivity,mean,?_,?_,?_,error_on_row wide un le_rfl⟩
  · intro u sub modle
    exact (intersection_error j t p i k diff large (below.trans cut) narrow
      (mul_nonneg ha sn) da est u sub modle).trans
      (mul_le_mul_of_nonneg_right (du a) (by positivity))
  · exact mul_nonneg (mul_nonneg (mul_nonneg ha sn) (by positivity)) lp
  · exact leading_bound ha (hn a) sn sb rn side' (volume_on_row wide) lp (pow_pos pp 2) lb
      cp (pow_pos gb _) prod

theorem congruences_from_mertens (quadric : PublishedQuadricCount) (mertens : PublishedMertensFour) :
    CongruenceInputs := congruences quadric (products_from_mertens mertens)

end
end Sun28.ConeCount
#print axioms Sun28.ConeCount.row_data
#print axioms Sun28.ConeCount.products_from_mertens
#print axioms Sun28.ConeCount.congruences
#print axioms Sun28.ConeCount.congruences_from_mertens
