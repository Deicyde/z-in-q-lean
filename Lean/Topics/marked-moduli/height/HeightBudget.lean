import PublicRankJoin
import ZInQKernel.Main

/-! Numerical use of the genus-two von Känel bound at the public multiplication primes. -/
namespace ZInQBlueprint.HeightBudget
open scoped BigOperators
open ZInQ ZInQBlueprint.PublicRankJoin

def primeProduct (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

noncomputable def conductorPrimes (S : Finset ℕ) (u : ℚ) : Finset ℕ :=
  S ∪ (contactSupport S u).primeFactors

/-- Each contact prime occurs once and lies outside S, so the requested inequality is an equality. -/
theorem conductor_product (S : Finset ℕ) (u : ℚ) :
    primeProduct (conductorPrimes S u) = primeProduct S * contactSupport S u := by
  classical
  unfold primeProduct conductorPrimes contactSupport
  rw [Nat.primeFactors_prod]
  · apply Finset.prod_union
    exact Finset.disjoint_left.mpr fun _ hs ht => (Finset.mem_filter.mp ht).2.1 hs
  · intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

private theorem card_of_bound (S : Finset ℕ) (D : ℕ) (hb : ∀ p ∈ S, 0 < p ∧ p ≤ D) :
    S.card ≤ D := by
  have h : S ⊆ Finset.Ioc 0 D := fun p hp => Finset.mem_Ioc.mpr (hb p hp)
  simpa only [Nat.card_Ioc, Nat.sub_zero] using Finset.card_le_card h

theorem S_mul_card : Mult.S_mul.card ≤ heightD :=
  card_of_bound _ _ (fun _ hp => ⟨(Mult.prime_of_mem_S_mul hp).pos, Mult.le_heightD_of_mem_S_mul hp⟩)

private theorem power_budget {S : Finset ℕ} {D E : ℕ} (hmax : ∀ p ∈ S, p ≤ D)
    (hcard : S.card ≤ D) (hD : 288 ≤ D) (hE : 2 ≤ E) :
    6^288 * (primeProduct S)^24 ≤ (D^(D*E))^17 := by
  have hprod : primeProduct S ≤ D^D :=
    (Finset.prod_le_pow_card S id D hmax).trans (Nat.pow_le_pow_right (by omega) hcard)
  have he : 288 + D*24 ≤ D*E*17 := by
    have hDE := Nat.mul_le_mul_left D hE
    omega
  calc
    _ ≤ D^288 * (D^D)^24 := Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 288) (Nat.pow_le_pow_left hprod 24)
    _ = D^(288 + D*24) := by rw [pow_add, pow_mul]
    _ ≤ D^(D*E*17) := Nat.pow_le_pow_right (by omega) he
    _ = _ := by rw [pow_mul]

private theorem two_le_E {D G : ℕ} (hD : 0 < D) (hG : 0 < G) :
    2 ≤ 10*(D*G)^2 := by
  have h := pow_pos (Nat.mul_pos hD hG) 2
  omega

/-- The base primes and the published coefficient are absorbed by exactly Q_D^17. -/
theorem constant_bound :
    (6:ℝ)^288 * (primeProduct Mult.S_mul : ℝ)^24 ≤ (heightQ (heightD : ℝ))^17 := by
  have hD : 288 ≤ heightD :=
    (by norm_num : 288 ≤ 10^12).trans Compiler.Precision.ten_pow_twelve_le_heightD
  have hE : 2 ≤ heightE0 := by
    rw [Compiler.Precision.heightE0_eq]
    exact two_le_E (by omega) (by norm_num [heightG0])
  rw [Compiler.Precision.heightQ_heightD,Compiler.Precision.Q0_eq]
  exact_mod_cast power_budget (S:=Mult.S_mul) (D:=heightD) (E:=heightE0)
    (fun _ hp => Mult.le_heightD_of_mem_S_mul hp) S_mul_card hD hE

/-- The genus-two specialization of (3g)^(144g) N_S^24 for the actual union of primes. -/
noncomputable def vonKaenelBudget (u : ℚ) : ℝ :=
  (6:ℝ)^288 * (primeProduct (conductorPrimes Mult.S_mul u) : ℝ)^24

/-- Exact third comparison of the archived PR24 join, for any stable height satisfying von Känel. -/
theorem third_comparison (u : ℚ) (stable : ℝ) (hv : stable ≤ vonKaenelBudget u) :
    max 1 stable ≤ max 1 (max (heightCcm:ℝ) (heightQ (heightD:ℝ)^17)) *
        (contactSupport Mult.S_mul u : ℝ)^24 := by
  let C := max 1 (max (heightCcm:ℝ) (heightQ (heightD:ℝ)^17))
  have hc : heightQ (heightD:ℝ)^17 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hm : (1:ℝ) ≤ contactSupport Mult.S_mul u := by exact_mod_cast contactSupport_pos _ _
  change max 1 stable ≤ C * _
  apply max_le
  · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hm)
  · calc
      stable ≤ vonKaenelBudget u := hv
      _ = ((6:ℝ)^288 * (primeProduct Mult.S_mul : ℝ)^24) * (contactSupport Mult.S_mul u : ℝ)^24 := by
        rw [vonKaenelBudget,conductor_product,Nat.cast_mul,mul_pow,mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right (constant_bound.trans hc) (by positivity)

/-- The two residual numerical inequalities after substituting the explicit bound for stable height. -/
def RemainingComparisons : Prop := ∀ u : ℚ, u ∉ contactSet → ∃ theta : ℝ,
  ratHeight (SixContact.J u) ≤ 40*theta+22 ∧
  theta ≤ (10000*2^24)*max 1 (vonKaenelBudget u)

/-- The original two comparisons for actual height values, together with von Känel, imply the residual form. -/
theorem remaining_of_heights {stable theta : ℚ → ℝ}
    (hVk : ∀ u, u ∉ contactSet → stable u ≤ vonKaenelBudget u)
    (hIgusa : ∀ u, u ∉ contactSet → ratHeight (SixContact.J u) ≤ 40*theta u+22)
    (hTheta : ∀ u, u ∉ contactSet → theta u ≤ (10000*2^24)*max 1 (stable u)) :
    RemainingComparisons := by
  intro u hu
  refine ⟨theta u, hIgusa u hu, (hTheta u hu).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (max_le_max_left 1 (hVk u hu)) (by positivity)

theorem geometry_of_remaining (h : RemainingComparisons) : GeometricComparisons Mult.S_mul := by
  intro u hu
  obtain ⟨theta, hi, ht⟩ := h u hu
  exact ⟨vonKaenelBudget u,theta,hi,ht,third_comparison u _ le_rfl⟩

theorem sixContactMin_of_remaining (h : RemainingComparisons) : SixContactMin :=
  sixContactMin_of_geometricComparisons (geometry_of_remaining h)

theorem frozen_of_remaining_and_class_rank (h : RemainingComparisons)
    (hRank : RouteK.Rank.CertifiedRankTYZClRk) : FrozenTarget :=
  frozen_of_geometry_and_class_rank (geometry_of_remaining h) hRank

#print axioms conductor_product
#print axioms S_mul_card
#print axioms constant_bound
#print axioms third_comparison
#print axioms remaining_of_heights
#print axioms geometry_of_remaining
#print axioms sixContactMin_of_remaining
#print axioms frozen_of_remaining_and_class_rank
end ZInQBlueprint.HeightBudget
