import PeriodDensityBound

namespace Sun28.PeriodWindows
open Finset
open scoped Classical
noncomputable section

/-- Fix a dyadic family N=2^(8t) so the small-modulus cutoff is exactly
N^(1/8). The two estimates are the fixed ray's prime number theorem and the
two exceptional residues per split prime in Huxley's theorem. -/
def RayCountEstimates (K : ℕ) : Prop :=
  ∃ c : ℝ, 0<c ∧ ∃ t₀ : ℕ, ∀ t≥t₀,
    let R:=2^t
    let N:=2^(8*t)
    let B:=c * (Nat.primeCounting N : ℝ)
    (15/16)*B ≤ ((primeBase K N).card:ℝ) ∧
    ∑ q∈splitPlaces K R, |((selfAt K N q).card:ℝ)-B*(2/((q:ℝ)-1)^2)| ≤ B/16

/-- This numerical predicate contains only the ordinary rational prime-counting
function. The prime number theorem gives both parts. -/
def PrimeGrowth : Prop :=
  (∀ c : ℝ, 0<c → ∃ t₀ : ℕ, ∀ t≥t₀,
    let N:=2^(8*t)
    (2*(N.sqrt:ℝ)+1)*(Nat.log 2 (N.sqrt^2+1):ℝ)*((2*(N.sqrt:ℝ)+1)/(2^t:ℕ)+1)
      ≤ c * (Nat.primeCounting N:ℝ)) ∧
  ∃ t₀ : ℕ, ∀ t≥t₀, Nat.primeCounting (2^(8*(t+1))) ≤ 512 * Nat.primeCounting (2^(8*t))

theorem positive_of_ray_estimates (K : ℕ) (est : RayCountEstimates K) (growth : PrimeGrowth) :
    PositivePrimeDensity (cleanPrime K) := by
  classical
  obtain ⟨c,cp,t₁,est⟩:=est
  obtain ⟨t₂,tail⟩:=growth.1 (c/8) (by positivity)
  obtain ⟨t₃,doubling⟩:=growth.2
  let T:=t₁+t₂+t₃+1
  refine ⟨c/1024,by positivity,2^(8*T),?_⟩
  intro N large
  let t:=Nat.log 2 N / 8
  have low:T≤t:=by
    apply (Nat.le_div_iff_mul_le (by decide : 0<8)).mpr
    rw [Nat.mul_comm]
    exact (Nat.le_log_iff_pow_le (by decide) (by
      exact Nat.ne_of_gt ((pow_pos (by decide : 0<2) (8*T)).trans_le large))).mpr large
  have tt₁:t₁≤t:=by dsimp [T] at low;omega
  have tt₂:t₂≤t:=by dsimp [T] at low;omega
  have tt₃:t₃≤t:=by dsimp [T] at low;omega
  have posT:0<t:=by dsimp [T] at low;omega
  have small:2^(8*t)≤N := by
    apply (Nat.le_log_iff_pow_le (by decide) (by
      exact Nat.ne_of_gt ((pow_pos (by decide : 0<2) (8*T)).trans_le large))).mp
    dsimp [t];omega
  have upper:N<2^(8*(t+1)) := by
    apply (Nat.log_lt_iff_lt_pow (by decide) (by
      exact Nat.ne_of_gt ((pow_pos (by decide : 0<2) (8*T)).trans_le large))).mp
    dsimp [t];omega
  have next : (Nat.primeCounting N:ℝ)≤512*(Nat.primeCounting (2^(8*t)):ℝ) := by
    exact_mod_cast (Nat.monotone_primeCounting upper.le).trans (doubling t tt₃)
  let M:=2^(8*t)
  let B:=c*(Nat.primeCounting M:ℝ)
  have bp:0≤B:=mul_nonneg cp.le (by positivity)
  obtain ⟨base,errors⟩:=est t tt₁
  have bound:=clean_lower K M (2^t) (by
    have e:=Nat.pow_le_pow_right (by decide : 0<2) (show 1≤t by omega)
    simpa using e) B (B/16) bp (by dsimp [B,M];linarith [base]) errors
  have tl:=tail t tt₂
  have h : B/2≤((cleanSet K M).card:ℝ) := by
    dsimp only [M,B] at *
    linarith
  have sub : cleanSet K M⊆cleanSet K N := by
    intro p hp
    obtain ⟨lo,yes⟩:=mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp lo).trans_le (Nat.add_le_add_right small 1)),yes⟩
  have count := (show ((cleanSet K M).card:ℝ)≤((cleanSet K N).card:ℝ) by exact_mod_cast card_le_card sub)
  change c/1024 * (Nat.primeCounting N:ℝ)≤ ((cleanSet K N).card:ℝ)
  have mult:=mul_le_mul_of_nonneg_left next cp.le
  dsimp only [B,M] at h
  linarith

theorem frames_of_standard_counts (narrow : NarrowTheorem) (growth : PrimeGrowth)
    (estimates : ∀ K,RayCountEstimates K) {X : ℤ} (w : Sun28.QualitativeRows.Window X) (L : ℕ) :
    Nonempty (PeriodFrame w L) :=
  frame_of_density narrow w L (positive_of_ray_estimates _ (estimates _) growth)

end
end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.positive_of_ray_estimates
#print axioms Sun28.PeriodWindows.frames_of_standard_counts
