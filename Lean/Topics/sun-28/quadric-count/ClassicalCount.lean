import LocalNormalization
import ConeMajorant
import RealDensity
import FlagApplication

namespace Sun28.ConeCount
open Finset Filter Topology Sun28.QuadricSieve Sun28.ConeSieve Sun28.ConeFibres
open ConeReal (tubeMass gradSq)
open scoped Classical ContDiff
noncomputable section

/-- Browning–Loughran, Theorem 4.1, with the real density of Heath-Brown,
Theorem 3, (1.3), for the integral rank-five family. The p-adic weights
and the nonnegative unrestricted product are fixed before choosing the test function. -/
def PublishedQuadricCount : Prop :=
  ∀ κ : ℤ, κ≠0 → ∃ (H : ℝ) (ρ : ℕ→ℝ),0≤H ∧ (∀ q,good κ q→0≤ρ q) ∧
    ∀ (R : ℕ) (ψ : Point ℝ→ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∀ x,0≤ψ x) → (∀ x∈tsupport ψ, ‖x‖≤(R:ℝ)) →
      (∀ x∈tsupport ψ, (1:ℝ)≤gradSq (κ:ℝ) x) →
      ∃ σ : ℝ,0≤σ ∧ Tendsto (fun ε=>tubeMass (κ:ℝ) ε ψ) (𝓝[>] 0) (𝓝 σ) ∧
        ∃ D : ℝ,0≤D ∧ Estimate κ R ψ (H*σ) D ρ

def localWeight (q : ℕ) : ℝ := (1-1/(q:ℝ)^3)/((q:ℝ)^4-1)

theorem primitive_card {κ : ℤ} {q : ℕ} (h : good κ q) :
    letI : NeZero q:=⟨h.1.ne_zero⟩
    ((primitive κ q).card:ℝ)=(q:ℝ)^4-1 := by
  let _ : Fact q.Prime:=⟨h.1⟩
  have eq : primitive κ q = nonzeroCone (κ:ZMod q) := by
    ext x;simp [primitive,nonzeroCone,normWindow,and_comm]
  rw [eq]
  exact_mod_cast nonzero_cone_card h.2.1 h.2.2

theorem per_class {κ R ψ S D ρ} (est : Estimate κ R ψ S D ρ) (sp : 0<S)
    {q : ℕ} (h : good κ q) : ρ q=localWeight q := by
  have normalize:=normalizes est sp q h
  let _ : NeZero q:=⟨h.1.ne_zero⟩
  change ρ q*((primitive κ q).card:ℝ)=_ at normalize
  rw [primitive_card h] at normalize
  have two : (2:ℝ)≤q:=by exact_mod_cast h.1.two_le
  have denom : 0<(q:ℝ)^4-1:=by nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) two 4]
  exact (eq_div_iff denom.ne').mpr normalize

theorem collision_classes {κ : ℤ} {q : ℕ} [Fact q.Prime] {x : Point (ZMod q)}
    (hx : x∈residues q κ) : onCone (κ:ZMod q) x ∧ x≠0 := by
  rcases mem_union.mp hx with a|b
  · obtain ⟨h,_,y⟩:=(mem_filter.mp a).2
    exact ⟨h,fun e=>by subst x;change (0:ZMod q)^2= -1 at y;simp at y⟩
  · exact ⟨(mem_filter.mp b).2.1,cross_nonzero b⟩

theorem collision_bound {κ : ℤ} {q : ℕ} [Fact q.Prime] (odd : q≠2) :
    0≤factor localWeight q (residues q κ) ∧
    factor localWeight q (residues q κ)≤16/(q:ℝ)^2 := by
  have two : (2:ℝ)≤q:=by exact_mod_cast (Fact.out : q.Prime).two_le
  have cub : (1:ℝ)≤(q:ℝ)^3:=one_le_pow₀ (by linarith : (1:ℝ)≤q)
  have denom : 0<(q:ℝ)^4-1:=by nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) two 4]
  have w : 0≤1-1/(q:ℝ)^3:=by linarith only [one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) cub]
  have count' : ((residues q κ).card:ℝ)≤8*(q:ℝ)^2:=by exact_mod_cast residues_card q odd κ
  constructor
  · exact mul_nonneg (div_nonneg w denom.le) (Nat.cast_nonneg _)
  · unfold factor localWeight
    have bound : (1-1/(q:ℝ)^3)/((q:ℝ)^4-1)≤1/((q:ℝ)^4-1):=by
      apply div_le_div_of_nonneg_right _ denom.le
      exact sub_le_self _ (by positivity)
    apply (mul_le_mul bound count' (Nat.cast_nonneg _) (by positivity)).trans
    apply (le_div_iff₀ (by positivity : 0<(q:ℝ)^2)).mpr
    field_simp [denom.ne']
    nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) two 4]

end
end Sun28.ConeCount
#print axioms Sun28.ConeCount.primitive_card
#print axioms Sun28.ConeCount.per_class
#print axioms Sun28.ConeCount.collision_classes
#print axioms Sun28.ConeCount.collision_bound
