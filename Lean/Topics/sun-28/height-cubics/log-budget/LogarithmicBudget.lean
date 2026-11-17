import PooledEndpoint

namespace Sun28.HeightCubics.Pooled.Logarithmic
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.MinimalConductors Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.HeightCubics.Refinement
noncomputable section
set_option maxRecDepth 2000

private theorem radical_large (A B:ℤ) : 62208≤heightRadical A B := by
  let P : Finset ℕ := {2,3,5,7,11,13,17}
  have small:P⊆oldCutoff:=by
    intro p h
    apply Finset.mem_filter.mpr
    have aux:∀ p∈P,p<76177 ∧ p.Prime:=by decide
    exact ⟨Finset.mem_range.mpr (aux p h).1,(aux p h).2⟩
  have prod:primeProduct P=510510:=by norm_num [P,primeProduct,Finset.prod_insert]
  have c:510510≤cutoffProduct:=prod ▸ support_mono small (fun _ h=>(Finset.mem_filter.mp h).2)
  have o:1≤oddProduct A B:=pos_odd A B
  change 62208≤cutoffProduct*oddProduct A B
  exact (show 62208≤510510 by decide).trans (c.trans (Nat.le_mul_of_pos_right _ o))

private theorem log_one {t:ℝ} (big:62208≤t) : 1≤Real.log t := by
  have low:=Real.log_le_log (by norm_num : (0:ℝ)<4) (show (4:ℝ)≤t by linarith)
  have neg:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2⁻¹)
  rw [Real.log_inv] at neg
  rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at low
  norm_num at low neg
  linarith only [low,neg]

/-- Retain both logarithms of the conductor when passing to Glazer's bound. -/
theorem absorb_log {m:ℕ} (pos : 0 < m) {t:ℝ} (large:62208≤t)
    (budget:(m:ℝ)*(Real.log t)^2≤62208*t^24) :
    heightBound m≤174960281*t^24 := by
  have t0:0<t:=by linarith
  have lg:=log_one large
  have lg2:1≤(Real.log t)^2:=one_le_pow₀ lg (n:=2)
  have m0:0<(m:ℝ):=by exact_mod_cast pos
  have m1:1≤(m:ℝ):=Nat.one_le_cast.mpr pos
  have upper:(m:ℝ)≤62208*t^24:=(le_mul_of_one_le_right m0.le lg2).trans budget
  have lc:=Real.log_le_log m0 upper
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ t0.ne'),Real.log_pow] at lc
  have fixed:=Real.log_le_log (by norm_num : (0:ℝ)<62208) large
  have bound:Real.log (m:ℝ)≤25*Real.log t:=by push_cast at lc;linarith only [lc,fixed]
  have sq:=pow_le_pow_left₀ (Real.log_nonneg m1) bound 2
  have comp:=mul_le_mul_of_nonneg_left sq m0.le
  have last:1≤t^24:=one_le_pow₀ (by linarith only [large]) (n:=24)
  unfold heightBound
  nlinarith only [comp,budget,last]

private theorem select {A B:ℤ}
    (h:(1225:ℝ)^5*(weight A B:ℝ)*(Real.log (heightRadical A B:ℝ))^10≤
      (heightRadical A B:ℝ)^120) : ChartTest A B := by
  let t : ℝ := heightRadical A B
  let l:=Real.log t
  have large:(62208:ℝ)≤t:=by change (62208:ℝ)≤(heightRadical A B:ℝ);exact_mod_cast radical_large A B
  have t0:0<t:=by linarith
  have done (i:Fin 5) (m:(cap (cycle i) A B:ℝ)*l^2≤62208*t^24) : ChartTest A B:=by
    have low:=absorb_log (cap_pos (cycle i) A B) large m
    have slack:(174960281:ℝ)≤2^810:=by
      exact (by norm_num : (174960281:ℝ)≤2^28).trans (pow_le_pow_right₀ (by norm_num) (by decide))
    exact ⟨cycle i,(low.trans (mul_le_mul_of_nonneg_right slack (pow_nonneg t0.le _))).trans (original_margin A B)⟩
  by_contra fail
  have big (i:Fin 5):62208*t^24<(cap (cycle i) A B:ℝ)*l^2:=lt_of_not_ge (fun e=>fail (done i e))
  have strict:(∏ _i:Fin 5,62208*t^24)<∏ i:Fin 5,(cap (cycle i) A B:ℝ)*l^2:=
    Finset.prod_lt_prod_of_nonempty₀ (fun _ _=>by positivity) (fun i _=>big i) Finset.univ_nonempty
  have capped:(∏i:Fin 5,(cap (cycle i) A B:ℝ))=(exceptional:ℝ)^5*(weight A B:ℝ):=by exact_mod_cast cyclic_product A B
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,capped] at strict
  have small:(62208:ℝ)^5*(1225^5*(weight A B:ℝ)*l^10)≤62208^5*t^120:=
    mul_le_mul_of_nonneg_left h (by positivity)
  have eq:(exceptional:ℝ)=62208*1225:=by exact_mod_cast (show exceptional=62208*1225 by decide)
  rw [eq] at strict
  nlinarith only [small,strict]

/-- All occurring large even orders, with the actual logarithmic allowance. -/
def Budget (A B:ℤ) : Prop :=
  (35:ℝ)^5*(classProduct oldCutoff .evenNoncube A B:ℝ)^3*(classProduct oldCutoff .evenCube A B:ℝ)*
    (Real.log (heightRadical A B:ℝ))^10 ≤
    6^5*(heightRadical A B:ℝ)^115*(classProduct oldCutoff .oddCube A B:ℝ)^2

private theorem combine {L O J H F C T z:ℝ} (l:0≤L) (o:0≤O) (j:0≤J)
    (low:210^5*L≤C^5) (rad:T=C*(O*J))
    (budget:35^5*H^3*F*z^10≤6^5*T^115*J^2) (t:0≤T) :
    1225^5*(L*(O^5*J^3*H^3*F))*z^10≤T^120 := by
  calc
    _ =(35^5*L*(O^5*J^3))*(35^5*H^3*F*z^10):=by ring
    _ ≤ (35^5*L*(O^5*J^3))*(6^5*T^115*J^2):=mul_le_mul_of_nonneg_left budget (by positivity)
    _ = (210^5*L)*(T^115*O^5*J^5):=by ring
    _ ≤ C^5*(T^115*O^5*J^5):=mul_le_mul_of_nonneg_right low (by positivity)
    _ = T^115*(C*(O*J))^5:=by ring
    _ = T^120:=by rw [←rad];ring

theorem chart_of_log {A B:ℤ} (cop:Int.gcd A B=1) (test:Budget A B) : ChartTest A B := by
  let C:=cutoffProduct
  let T:=heightRadical A B
  let L:=lowWeight A B
  let O:=classProduct oldCutoff .oddNoncube A B
  let J:=classProduct oldCutoff .oddCube A B
  let H:=classProduct oldCutoff .evenNoncube A B
  let F:=classProduct oldCutoff .evenCube A B
  have old:oddProduct A B=O*J:=odd_classes cop
  have id:T=C*(O*J):=by change cutoffProduct*oddProduct A B=_;rw [old]
  have factor:weight A B=L*(O^5*J^3*H^3*F):=split_weight A B
  have low:(210:ℝ)^5*(L:ℝ)≤(C:ℝ)^5:=by exact_mod_cast low_weight_bound cop
  have T':(T:ℝ)=(C:ℝ)*((O:ℝ)*(J:ℝ)):=by exact_mod_cast id
  apply select
  rw [factor]
  push_cast
  exact combine (by positivity) (by positivity) (by positivity) low T' test (by positivity)

end
end Sun28.HeightCubics.Pooled.Logarithmic
#print axioms Sun28.HeightCubics.Pooled.Logarithmic.absorb_log
#print axioms Sun28.HeightCubics.Pooled.Logarithmic.chart_of_log
