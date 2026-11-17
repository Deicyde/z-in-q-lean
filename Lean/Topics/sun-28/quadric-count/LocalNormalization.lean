import PrimitiveCount
namespace Sun28.ConeCount
open Finset Filter Topology
open scoped Classical
noncomputable section

def modulus (s : Finset ℕ) := ∏ q∈s,q

def factor (ρ : ℕ→ℝ) (q : ℕ) (V : Finset (Point (ZMod q))) := ρ q * V.card

def main (ρ : ℕ→ℝ) (s : Finset ℕ) (V : Classes) := ∏ q∈s,factor ρ q (V q)

def Estimate (κ : ℤ) (R : ℕ) (ψ : Point ℝ→ℝ) (S D : ℝ) (ρ : ℕ→ℝ) : Prop :=
  ∀ B : ℕ, 0<B → ∀ s : Finset ℕ, (∀ q∈s,good κ q) →
    ∀ V : Classes, (∀ q∈s,∀ x∈V q,Sun28.QuadricSieve.onCone (κ:ZMod q) x ∧ x≠0) →
    |count κ R B ψ s V - S*(B:ℝ)^3*main ρ s V| ≤ D*((B:ℝ)*modulus s)^(13/5:ℝ)

theorem entire_estimate {κ R ψ S D ρ} (h : Estimate κ R ψ S D ρ) (B : ℕ) (b : 0<B) :
    |entire κ R B ψ - S*(B:ℝ)^3|≤D*(B:ℝ)^(13/5:ℝ) := by
  have e:= h B b ∅ (by simp) (fun _=>∅) (by simp)
  have all : (coneBox κ R B).filter (accepts ∅ (fun _=>∅)) = coneBox κ R B := by
    apply filter_true_of_mem; intro x _; simp [accepts]
  simpa [count,entire,all,main,modulus] using e

/-- For a fixed modulus an error of order B^(13/5) determines the B³ coefficient. -/
theorem coefficient_limit {f : ℕ→ℝ} {s D : ℝ}
    (bound : ∀ B : ℕ,0<B→|f B-s*(B:ℝ)^3|≤D*(B:ℝ)^(13/5:ℝ)) :
    Tendsto (fun B : ℕ=>f B/(B:ℝ)^3) atTop (𝓝 s) := by
  have t:= (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<2/5)).comp tendsto_natCast_atTop_atTop
  have lim:=t.const_mul D
  rw [mul_zero] at lim
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  filter_upwards [lim.eventually_lt_const ep,eventually_ge_atTop (1:ℕ)] with B small pos
  have b : (0:ℝ)<B:=by exact_mod_cast pos
  have eq : (B:ℝ)^(13/5:ℝ)/(B:ℝ)^3=(B:ℝ)^(-(2/5):ℝ) := by
    rw [←Real.rpow_natCast (B:ℝ) 3,←Real.rpow_sub b];norm_num
  rw [Real.dist_eq,div_sub' (by positivity : (B:ℝ)^3≠0),mul_comm ((B:ℝ)^3) s,abs_div,abs_of_pos (pow_pos b 3)]
  apply lt_of_le_of_lt (div_le_div_of_nonneg_right (bound B pos) (by positivity))
  rw [mul_div_assoc,eq];exact small

/-- Dilation by q transports the normalized main term by the factor q³. -/
private theorem dilated_limit {f : ℕ→ℝ} {s D : ℝ}
    (h : ∀ B : ℕ,0<B→|f B-s*(B:ℝ)^3|≤D*(B:ℝ)^(13/5:ℝ)) {q : ℕ} (qp:0<q) :
    Tendsto (fun B : ℕ=>f (q*B)/(B:ℝ)^3) atTop (𝓝 (s*(q:ℝ)^3)) := by
  have up : Tendsto (fun B : ℕ=>q*B) atTop atTop :=
    tendsto_atTop.mpr (fun a=> (eventually_ge_atTop a).mono (fun B le=>le.trans
      (by simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right B qp)))
  have limit:=((coefficient_limit h).comp up).mul_const ((q:ℝ)^3)
  apply limit.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with B pos
  change f (q*B)/((q*B:ℕ):ℝ)^3*(q:ℝ)^3=f (q*B)/(B:ℝ)^3
  push_cast
  field_simp [show (B:ℝ)≠0 by positivity,show (q:ℝ)≠0 by positivity]

/-- The full-cone fraction of nonzero residue classes follows from the
homogeneity of the integral points, with no lifting calculation at prime powers. -/
theorem normalizes {κ R ψ S D ρ} (est : Estimate κ R ψ S D ρ) (sp : 0<S)
    (q : ℕ) (goodq : good κ q) :
    letI : NeZero q := ⟨goodq.1.ne_zero⟩
    factor ρ q (primitive κ q)=1-1/(q:ℝ)^3 := by
  let _ : NeZero q:=⟨goodq.1.ne_zero⟩
  let V:=single q (primitive κ q)
  let m:=factor ρ q (primitive κ q)
  have nonzero := fun (B : ℕ) (b : 0<B)=>est B b {q} (by simpa using goodq) V (by
    intro p hp x hx;obtain rfl:=mem_singleton.mp hp
    simpa [V,single,primitive] using hx)
  have keep (B : ℕ) (b : 0<B) : |count κ R B ψ {q} V-(S*m)*(B:ℝ)^3| ≤
      (D*(q:ℝ)^(13/5:ℝ))*(B:ℝ)^(13/5:ℝ) := by
    have e:=nonzero B b
    simp only [modulus,prod_singleton,Real.mul_rpow (Nat.cast_nonneg B) (Nat.cast_nonneg q)] at e
    simpa [main,V,single,m,
      mul_comm,mul_left_comm,mul_assoc] using e
  have left:=dilated_limit keep goodq.1.pos
  have right:=(dilated_limit (entire_estimate est) goodq.1.pos).sub (coefficient_limit (entire_estimate est))
  have diff : Tendsto (fun B : ℕ=>count κ R (q*B) ψ {q} V /(B:ℝ)^3) atTop (𝓝 (S*(q:ℝ)^3-S)) := by
    simpa [V,primitive_diff,sub_div] using right
  have eq:=tendsto_nhds_unique left diff
  change (S*m)*(q:ℝ)^3=S*(q:ℝ)^3-S at eq
  change m=1-1/(q:ℝ)^3
  have qn : (q:ℝ)≠0:=by exact_mod_cast goodq.1.ne_zero
  field_simp [qn]
  apply mul_left_cancel₀ sp.ne'
  linarith only [eq]

end
end Sun28.ConeCount
#print axioms Sun28.ConeCount.entire_estimate
#print axioms Sun28.ConeCount.coefficient_limit
#print axioms Sun28.ConeCount.normalizes
