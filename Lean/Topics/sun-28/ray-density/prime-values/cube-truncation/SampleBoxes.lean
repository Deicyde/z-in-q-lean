import LocalizedAverage

namespace Sun28.CubeTruncation
open Sun28.AffinePullback Finset
noncomputable section

/-- Ordered pairs in a finite interval, with the same multiplicities as the local box. -/
def pairs (m : ℕ) := (range m) ×ˢ (range m)

theorem rect_mono {k m : ℕ} (inc : k≤m) {f g : ℕ→ℕ→ℝ}
    (dom : ∀ i j, f i j ≤ g i j) (pos : ∀ i j, 0 ≤ g i j) :
    ∑ i∈range k, ∑ j∈range k, f i j ≤ ∑ i∈range m, ∑ j∈range m, g i j := by
  have subset : pairs k ⊆ pairs m := Finset.product_subset_product (Finset.range_mono inc) (Finset.range_mono inc)
  calc
    _ = ∑ u ∈ pairs k, f u.1 u.2 := (Finset.sum_product' ..).symm
    _ ≤ ∑ u ∈ pairs k, g u.1 u.2 := Finset.sum_le_sum (fun u _ => dom u.1 u.2)
    _ ≤ ∑ u ∈ pairs m, g u.1 u.2 := Finset.sum_le_sum_of_subset_of_nonneg subset (fun u _ _ => pos u.1 u.2)
    _ = _ := Finset.sum_product' ..

/-- Sum of an arbitrary real kernel over both index copies in every direction and all base points. -/
def sampleSum (n : ℕ) [NeZero n] : (a:ℕ) → (Fin a→ℕ) →
    ((Fin a→ℕ×ℕ)→ZMod n→ℝ) → ℝ
  | 0, _, K => ∑ x : ZMod n, K Fin.elim0 x
  | a+1, m, K => ∑ i∈range (m 0), ∑ j∈range (m 0),
      sampleSum n a (fun k => m k.succ) (fun s => K (Fin.cons (i,j) s))

theorem sample_add (n : ℕ) [NeZero n] (a : ℕ) (m : Fin a→ℕ)
    (K L : (Fin a→ℕ×ℕ)→ZMod n→ℝ) :
    sampleSum n a m (fun s x => K s x+L s x) = sampleSum n a m K + sampleSum n a m L := by
  induction a with
  | zero => simp [sampleSum,Finset.sum_add_distrib]
  | succ a ih =>
    simp only [sampleSum]
    simp_rw [ih]
    simp only [Finset.sum_add_distrib]

theorem sample_const (n : ℕ) [NeZero n] (a : ℕ) (m : Fin a→ℕ) (c : ℝ) :
    sampleSum n a m (fun _ _ => c)=n*(∏ i : Fin a,(m i:ℝ)^2)*c := by
  induction a with
  | zero => simp [sampleSum,ZMod.card, nsmul_eq_mul]
  | succ a ih =>
    simp only [sampleSum, ih]
    rw [Fin.prod_univ_succ]
    simp [nsmul_eq_mul]
    ring

theorem sample_nonneg (n : ℕ) [NeZero n] (a : ℕ) (m : Fin a→ℕ)
    (K : (Fin a→ℕ×ℕ)→ZMod n→ℝ) (pos : ∀ s x, 0≤K s x) :
    0≤ sampleSum n a m K := by
  induction a with
  | zero => exact Finset.sum_nonneg (fun x _ => pos _ x)
  | succ a ih =>
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact ih _ _ (fun s x => pos _ x)

theorem sample_mono (n : ℕ) [NeZero n] (a : ℕ) (k m : Fin a→ℕ)
    (inc : ∀ i, k i≤m i) (K : (Fin a→ℕ×ℕ)→ZMod n→ℝ) (pos : ∀ s x, 0≤K s x) :
    sampleSum n a k K ≤ sampleSum n a m K := by
  induction a with
  | zero => rfl
  | succ a ih =>
    apply rect_mono (inc 0)
    · intro i j
      exact ih _ _ (fun i => inc i.succ) _ (fun s x => pos _ x)
    · intro i j
      exact sample_nonneg n a (fun i => m i.succ) (fun s => K (Fin.cons (i,j) s)) (fun s x => pos _ x)

/-- The discarded part of a signed sum over two genuinely nested boxes. -/
theorem sample_discard (n : ℕ) [NeZero n] (a : ℕ) (k m : Fin a→ℕ)
    (inc : ∀ i,k i≤m i) (K : (Fin a→ℕ×ℕ)→ZMod n→ℝ) (C : ℝ)
    (bound : ∀ s x, |K s x|≤C) :
    |sampleSum n a m K-sampleSum n a k K| ≤
      (n*(∏ i :Fin a,(m i:ℝ)^2)-n*(∏ i :Fin a,(k i:ℝ)^2))*C := by
  have high := sample_mono n a k m inc (fun s x => C + K s x) (fun s x => by
    have := (abs_le.mp (bound s x)).1; linarith)
  have low := sample_mono n a k m inc (fun s x => -K s x + C) (fun s x => by
    have := (abs_le.mp (bound s x)).2; linarith)
  have neg (j : Fin a→ℕ) : sampleSum n a j (fun s x => -K s x) = -(sampleSum n a j K) := by
    have ez := sample_add n a j (fun s x => -K s x) K
    simp only [neg_add_cancel] at ez
    rw [sample_const] at ez
    linarith
  have upper (j : Fin a→ℕ) :
      sampleSum n a j (fun s x => C+K s x) = n*(∏ i:Fin a,(j i:ℝ)^2)*C + sampleSum n a j K :=
    (sample_add n a j (fun _ _ => C) K).trans (by rw [sample_const])
  have lower (j : Fin a→ℕ) :
      sampleSum n a j (fun s x => -K s x+C) = -(sampleSum n a j K) + n*(∏ i:Fin a,(j i:ℝ)^2)*C :=
    (sample_add n a j (fun s x => -K s x) (fun _ _ => C)).trans (by rw [neg,sample_const])
  rw [upper,upper] at high
  rw [lower,lower] at low
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end Sun28.CubeTruncation
#print axioms Sun28.CubeTruncation.sample_const
#print axioms Sun28.CubeTruncation.sample_mono
#print axioms Sun28.CubeTruncation.sample_discard
