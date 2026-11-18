module

public import Std

@[expose] public section

namespace OddMinimum

/-- The property holds at arbitrarily late stages. -/
def Often (P : Nat → Prop) : Prop := ∀ b, ∃ i, b ≤ i ∧ P i

private theorem eventually_avoids {P : Nat → Prop} (h : ¬Often P) :
    ∃ b, ∀ i, b ≤ i → ¬P i := by
  classical
  simpa only [Often, Classical.not_forall, not_exists, not_and] using h

theorem bounded_pigeonhole (P : Nat → Nat → Prop) (r : Nat)
    (h : Often fun i => ∃ d, d ≤ r ∧ P i d) :
    ∃ d, d ≤ r ∧ Often (fun i => P i d) := by
  classical
  induction r with
  | zero =>
    refine ⟨0, Nat.le_refl _, fun b => ?_⟩
    obtain ⟨i, hi, d, hd, hp⟩ := h b
    have : d = 0 := by omega
    exact ⟨i, hi, this ▸ hp⟩
  | succ r ih =>
    by_cases top : Often (fun i => P i (r + 1))
    · exact ⟨r + 1, Nat.le_refl _, top⟩
    obtain ⟨b, hb⟩ := eventually_avoids top
    have lower : Often (fun i => ∃ d, d ≤ r ∧ P i d) := by
      intro n
      obtain ⟨i, hi, d, hd, hp⟩ := h (max b n)
      have hne : d ≠ r + 1 := fun e => hb i (by omega) (e ▸ hp)
      exact ⟨i, by omega, d, by omega, hp⟩
    obtain ⟨d, hd, hp⟩ := ih lower
    exact ⟨d, by omega, hp⟩

private theorem least {P : Nat → Prop} {n : Nat} (h : P n) :
    ∃ d, P d ∧ ∀ e, e < d → ¬P e := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases lower : ∃ e, e < n ∧ P e
    · obtain ⟨e, he, hp⟩ := lower
      exact ih e he hp
    · exact ⟨n, h, fun e he hp => lower ⟨e, he, hp⟩⟩

/-- P i W d means that stage i has a visible entry of weight at most W and
    depth d above the common integer floor. No bound on the Fourier index
    or compatibility between successive stages is assumed. -/
theorem recurrent_minimum (P : Nat → Nat → Nat → Prop)
    (seed : ∃ w r, Often fun i => ∃ d, d ≤ r ∧ P i w d) :
    ∃ d w, Often (fun i => P i w d) ∧
      ∀ W, ∃ b, ∀ i, b ≤ i → ∀ e, P i W e → d ≤ e := by
  classical
  obtain ⟨w, r, hs⟩ := seed
  obtain ⟨e, _, he⟩ := bounded_pigeonhole (fun i j => P i w j) r hs
  obtain ⟨d, ⟨w₀, hw⟩, hleast⟩ :=
    least (P := fun j => ∃ W, Often (fun i => P i W j)) (n := e) ⟨w, he⟩
  refine ⟨d, w₀, hw, fun W => ?_⟩
  have hbad : ¬Often (fun i => ∃ e, e < d ∧ P i W e) := by
    intro bad
    have small : Often (fun i => ∃ e, e ≤ d - 1 ∧ e < d ∧ P i W e) := by
      intro b
      obtain ⟨i, hi, e, hd, hp⟩ := bad b
      exact ⟨i, hi, e, by omega, hd, hp⟩
    obtain ⟨e, _, frequent⟩ :=
      bounded_pigeonhole (fun i j => j < d ∧ P i W j) (d - 1) small
    obtain ⟨_, _, hd, _⟩ := frequent 0
    apply hleast e hd
    refine ⟨W, fun b => ?_⟩
    obtain ⟨i, hi, _, hp⟩ := frequent b
    exact ⟨i, hi, hp⟩
  obtain ⟨b, hb⟩ := eventually_avoids hbad
  refine ⟨b, fun i hi e hp => ?_⟩
  have : ¬ e < d := fun hd => hb i hi ⟨e, hd, hp⟩
  omega

#print axioms bounded_pigeonhole
#print axioms recurrent_minimum

end OddMinimum
