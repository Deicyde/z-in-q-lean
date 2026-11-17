import FlagCounts
import RowEstimates
import ConeEuler
namespace Sun28.ConeCount
open Finset Filter Topology Sun28.ConeSieve Sun28.QuadricSieve Sun28.ConeFibres Sun28.ConeEuler
open Sun28.ContactFactors Sun28.WeightedSelection Sun28.SieveTail Sun28.SinglePrime Sun28.MediumSieve
open scoped Classical
noncomputable section

def threshold (A : Fin 3→ℚ) := max 64 (exceptionalBound A 1)

theorem good_gap {A : Fin 3→ℚ} {i k : ↥(shifts A)} (diff : i≠k) {q : ℕ}
    (pr : q.Prime) (large : threshold A<q) : good (gap i k) q := by
  let _ : Fact q.Prime:=⟨pr⟩
  have b:=lt_of_le_of_lt (le_max_right 64 (exceptionalBound A 1)) large
  have c:=lt_of_le_of_lt (le_max_left 64 (exceptionalBound A 1)) large
  exact ⟨pr,by omega,reduced_gap_ne_zero (by decide : 0<1) b diff⟩

theorem flag_approximation {A : Fin 3→ℚ} (i k : ↥(shifts A)) (diff : i≠k) :
    LocalApproximation (threshold A) (shifts A).card 50 (density i k) := by
  intro q pr large
  let _ : Fact q.Prime:=⟨pr⟩
  have goodq:=good_gap diff pr large
  have two : (2:ℝ)≤q := by exact_mod_cast pr.two_le
  have cub : (1:ℝ)≤(q:ℝ)^3 := one_le_pow₀ (by linarith : (1:ℝ)≤q)
  have wn : 0≤1-1/(q:ℝ)^3 := by linarith only [one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) cub]
  have den : 0≤(q:ℝ)^4-1 := by nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) two 4]
  refine ⟨mul_nonneg (div_nonneg wn den) (Nat.cast_nonneg _),?_⟩
  rw [density_eq]
  exact full_density_error_mod_four (by decide : 0<1)
    (lt_of_le_of_lt (le_max_right ..) large) goodq.2.1 i k diff

theorem normalized_main {κ R ψ S D ρ} (est : Estimate κ R ψ S D ρ) (sn : 0≤S)
    (B : ℕ) (s : Finset ℕ) (V : Classes) (good' : ∀ q∈s,good κ q) :
    S*(B:ℝ)^3*main ρ s V = S*(B:ℝ)^3*main localWeight s V := by
  rcases sn.eq_or_lt with zero|pos
  · rw [←zero];simp
  · congr 1
    apply prod_congr rfl
    intro q h
    rw [factor,per_class est pos (good' q h)]
    rfl

theorem intersection_error {A : Fin 3→ℚ} (j t p : ℕ) [Fact p.Prime] (i k : ↥(shifts A))
    (diff : i≠k) (large : threshold A<p) (hp : p≤level t) (narrow : 8*(maxCoefficient A+1)≤j+1)
    {S D ρ} (sn : 0≤S) (dn : 0≤D) (est : Estimate (gap i k) 2 (ConeReal.weight j) S D ρ)
    (u : Finset ℕ) (sub : u⊆auxPrimes (threshold A) (smallLevel t) p) (hm : modulus u≤(level t)^2) :
    let P:=auxPrimes (threshold A) (smallLevel t) p
    let F:=ConeReal.majorant j t p i k narrow
    |intersections F.support F.weight (badFactors i P) u -
      (S*(side t:ℝ)^3*factor localWeight p (residues p (gap i k)))*(∏ q∈u,density i k q)| ≤
        D*(2:ℝ)^(559*t) := by
  let P:=auxPrimes (threshold A) (smallLevel t) p
  have out : p∉P:=fun h=>(mem_auxPrimes.mp h).2.2.2 rfl
  have ou : p∉u:=fun h=>out (sub h)
  have g (q : ℕ) (h : q∈insert p u) : good (gap i k) q := by
    rcases mem_insert.mp h with rfl|h
    · exact good_gap diff Fact.out large
    · have a:=mem_auxPrimes.mp (sub h)
      exact good_gap diff a.1 a.2.1
  have e:=est (side t) (by unfold side;positivity) (insert p u) g (classes i k p)
    (fun q h _ hx=>all_classes i k p q (g q h).1 hx)
  rw [normalized_main est sn _ _ _ g,main_factors i k p u ou] at e
  have m : modulus (insert p u)=p*modulus u:=prod_insert ou
  rw [m,Nat.cast_mul] at e
  dsimp only
  rw [counted_flags j t p i k narrow P u (fun q h=>(mem_auxPrimes.mp h).1) out sub]
  apply le_trans _ (mul_le_mul_of_nonneg_left (discrepancy_power hp hm) dn)
  simpa only [mul_assoc] using e

theorem leading_bound {H Z σ c τ R B N a d g Q : ℝ}
    (hn : 0≤H) (hz : H≤Z) (sn : 0≤σ) (sb : σ≤R*τ) (rn : 0≤R)
    (bn : 0≤B) (vol : τ*B^3≤2*N) (an : 0≤a) (dp : 0<d) (ab : a≤16/d)
    (cp : 0<c) (gp : 0<g) (prod : c*g≤Q) :
    2*(H*σ*B^3*a)/Q≤(64*Z*R/c)*N/(d*g) := by
  have zn:=hn.trans hz
  have nonrad : 0≤R*τ := sn.trans sb
  calc
    _ ≤ 2*(Z*(R*τ)*B^3*(16/d))/(c*g) := by
      apply div_le_div₀ (by positivity) _ (mul_pos cp gp) prod
      gcongr
    _ = (32*Z*R)*(τ*B^3)/(c*d*g) := by field_simp;ring
    _ ≤ (32*Z*R)*(2*N)/(c*d*g) := by gcongr
    _ = _ := by field_simp;ring

end
end Sun28.ConeCount
#print axioms Sun28.ConeCount.flag_approximation
#print axioms Sun28.ConeCount.normalized_main
#print axioms Sun28.ConeCount.intersection_error
#print axioms Sun28.ConeCount.leading_bound
