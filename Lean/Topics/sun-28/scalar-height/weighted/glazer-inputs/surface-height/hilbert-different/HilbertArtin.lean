import ZInQKernel.Contrib.HilbertDifferent.T21
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Tactic

/-! A dimension bound for the lower-numbering Artin conductor, with the
Hilbert different formula and Serre's inequality on the same number-field prime.
The invariant spaces are those of an actual representation of its decomposition group.
The same-field ideal comparison follows the upstream D1 proof, with a new conductor
endpoint. See the source manifest for the pinned upstream imports and attributions. -/

open NumberField Finset
open scoped NumberField Pointwise
open ZInQKernel.Contrib.HilbertDifferent

namespace Sun28.SurfaceHeight.HilbertArtin

variable (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
variable (p : ℕ) [hpFact : Fact p.Prime]
variable (P : Ideal (𝓞 L)) [P.IsPrime] [hPp : P.LiesOver (Ideal.span {(p : ℤ)})]

/-- The nonnegative part of Hilbert's different sum beyond the tame term.
The assertion applies to the true lower filtration and allows every truncation. -/
theorem wild_different_le (n : ℕ) :
    ∑ j ∈ range n, (ramCard L P (j+1) - 1) ≤
      P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) := by
  have hp := (Fact.out : p.Prime)
  have hP0 : P ≠ ⊥ := by
    intro h
    have h' := hPp.over
    rw [h, Ideal.under_bot] at h'
    have hz := Ideal.span_singleton_eq_bot.mp h'
    simp [hp.ne_zero] at hz
  obtain ⟨m, hm, hdvd, _⟩ := hilbertDifferentFormula L P hP0
  let g := ramCard L P
  have hmono : Antitone g := by
    intro i j hij
    apply Subgroup.card_le_of_le
    intro σ hσ x
    exact Ideal.pow_le_pow_right (by omega) (hσ x)
  have htail (j : ℕ) (hj : m ≤ j) : g j = 1 := by
    have hmin : g j ≤ g m := hmono hj
    have hone : g m = 1 := by
      change Nat.card (ramGroup L P m) = 1
      rw [hm, Subgroup.card_bot]
    have hpos : 0 < g j := Nat.card_pos
    omega
  have hmonoSum (a b : ℕ) (hab : a ≤ b) :
      ∑ j ∈ range a, (g j - 1) ≤ ∑ j ∈ range b, (g j - 1) :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hab)
  have htotal : ∑ j ∈ range (n+1), (g j - 1) ≤ ∑ j ∈ range m, (g j - 1) := by
    by_cases hn : n+1 ≤ m
    · exact hmonoSum _ _ hn
    · have hmn : m ≤ n+1 := by omega
      apply le_of_eq
      symm
      apply Finset.sum_subset (Finset.range_mono hmn)
      intro j hj hnot
      have hj' : m ≤ j := by simpa using hnot
      simp [htail j hj']
  have he : g 0 = P.ramificationIdx ℤ := by
    show Nat.card ((P ^ (0+1)).inertia Gal(L/ℚ)) = _
    rw [zero_add, pow_one, Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(p : ℤ)}) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(L/ℚ)]
  have hSer := serreDifferentBound L p hp P hPp
  have hsum : ∑ j ∈ range m, (g j - 1) ≤ g 0 - 1 + g 0 * padicValNat p (g 0) := by
    rw [he]
    by_contra hlt
    push Not at hlt
    exact hSer (dvd_trans (pow_dvd_pow P hlt) hdvd)
  have h := htotal.trans hsum
  rw [Finset.sum_range_succ', he] at h
  change ∑ j ∈ range n, (g (j+1) - 1) ≤ _
  omega

/-- Denominator-cleared upper bound for the finite lower-numbering Swan sum with
any dimension weights zero when the corresponding group is trivial. -/
theorem weighted_wild_le (d n : ℕ) (c : ℕ → ℕ)
    (well_defined : ∀ i, ramGroup L P (i+1) = ⊥ → c i = 0)
    (bounded : ∀ i, c i ≤ d) :
    (∑ j ∈ range n, ramCard L P (j+1) * c j) ≤
      2 * d * (P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ)) := by
  have term (j : ℕ) :
      ramCard L P (j+1) * c j ≤ 2*d*(ramCard L P (j+1)-1) := by
    by_cases h : ramGroup L P (j+1) = ⊥
    · simp [well_defined j h]
    · have hpos : 0 < ramCard L P (j+1) := Nat.card_pos
      have hne : ramCard L P (j+1) ≠ 1 := fun h1 => h (Subgroup.card_eq_one.mp h1)
      have hs : ramCard L P (j+1) ≤ 2*(ramCard L P (j+1)-1) := by omega
      calc
        _ ≤ (2*(ramCard L P (j+1)-1))*d := Nat.mul_le_mul hs (bounded j)
        _ = _ := by ring
  calc
    _ ≤ ∑ j ∈ range n, 2*d*(ramCard L P (j+1)-1) := Finset.sum_le_sum (fun j _ => term j)
    _ = 2*d*(∑ j ∈ range n, (ramCard L P (j+1)-1)) := (Finset.mul_sum ..).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (wild_different_le L p P n)

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

abbrev decompositionGroup := MulAction.stabilizer (L ≃ₐ[ℚ] L) P

noncomputable def fixedCodim (ρ : Representation k (decompositionGroup L P) V) (j : ℕ) : ℕ :=
  Module.finrank k V - Module.finrank k
    (Representation.invariants (ρ.comp (Subgroup.inclusion (P.ramificationGroup_le_stabilizer (G := L ≃ₐ[ℚ] L) j))))

omit [IsGalois ℚ L] [P.IsPrime] in
theorem fixedCodim_eq_zero (ρ : Representation k (decompositionGroup L P) V) (j : ℕ)
    (h : ramGroup L P j = ⊥) : fixedCodim L P ρ j = 0 := by
  have heq : Representation.invariants (ρ.comp (Subgroup.inclusion
      (P.ramificationGroup_le_stabilizer (G := L ≃ₐ[ℚ] L) j))) = ⊤ := by
    apply top_unique
    intro v _ g
    have hg : g.1 ∈ ramGroup L P j := g.2
    rw [h, Subgroup.mem_bot] at hg
    have hg' : g = 1 := Subtype.ext hg
    simp [hg']
  have hdim := congrArg (fun W : Submodule k V => Module.finrank k W) heq
  have htop : Module.finrank k (⊤ : Submodule k V) = Module.finrank k V := by simp
  exact Nat.sub_eq_zero_of_le (hdim.trans htop).ge

/-- Truncation after the last nontrivial lower group is the standard Artin sum.
The inequality already holds for every finite truncation. -/
noncomputable def artinPartial (ρ : Representation k (decompositionGroup L P) V) (n : ℕ) : ℚ :=
  (fixedCodim L P ρ 0 : ℚ) +
    (∑ j ∈ range n, ramCard L P (j+1) * fixedCodim L P ρ (j+1) : ℕ) /
      (P.ramificationIdx ℤ : ℚ)

theorem artinPartial_le (ρ : Representation k (decompositionGroup L P) V) (n : ℕ) :
    artinPartial L P ρ n ≤ (Module.finrank k V : ℚ) *
      (1 + 2*(padicValNat p (P.ramificationIdx ℤ) : ℚ)) := by
  let d := Module.finrank k V
  let e := P.ramificationIdx ℤ
  have he : 0 < e := Ideal.ramificationIdx_pos ℤ P
  have hc (j : ℕ) : fixedCodim L P ρ j ≤ d := Nat.sub_le _ _
  have w := weighted_wild_le L p P d n (fun j => fixedCodim L P ρ (j+1))
    (fun j => fixedCodim_eq_zero L P ρ (j+1)) (fun j => hc (j+1))
  have hr : (0:ℚ) < e := by exact_mod_cast he
  have hq :
      (∑ j ∈ range n, ramCard L P (j+1) * fixedCodim L P ρ (j+1) : ℕ) /
        (e : ℚ) ≤ 2*(d : ℚ)*padicValNat p e := by
    apply (div_le_iff₀ hr).2
    norm_cast
    simpa [mul_assoc, mul_comm, mul_left_comm, e] using w
  have ht : (fixedCodim L P ρ 0 : ℚ) ≤ d := by exact_mod_cast hc 0
  change (fixedCodim L P ρ 0 : ℚ) + _ ≤ (d : ℚ) * (1+2*(padicValNat p e : ℚ))
  linarith

include hpFact hPp in
/-- Every lower group beyond one actual terminating index is trivial. -/
theorem exists_termination : ∃ n, ∀ i, n ≤ i → ramGroup L P i = ⊥ := by
  have hp := (Fact.out : p.Prime)
  have hP0 : P ≠ ⊥ := by
    intro h
    have h' := hPp.over
    rw [h, Ideal.under_bot] at h'
    have hz := Ideal.span_singleton_eq_bot.mp h'
    simp [hp.ne_zero] at hz
  obtain ⟨n, hn, _, _⟩ := hilbertDifferentFormula L P hP0
  refine ⟨n, fun i hi => ?_⟩
  apply eq_bot_iff.mpr
  rw [← hn]
  intro σ hσ x
  exact Ideal.pow_le_pow_right (by omega) (hσ x)

/-- The finite lower-numbering Artin sum beyond the last nontrivial group.
Its value is independent of the choice of terminating index. -/
noncomputable def artinConductor (ρ : Representation k (decompositionGroup L P) V) : ℚ :=
  artinPartial L P ρ (Classical.choose (exists_termination L p P))

theorem artinConductor_eq_of_termination (ρ : Representation k (decompositionGroup L P) V)
    (n : ℕ) (stops : ∀ i, n ≤ i → ramGroup L P i = ⊥) :
    artinConductor L p P ρ = artinPartial L P ρ n := by
  let cut := Classical.choose (exists_termination L p P)
  have hcut : ∀ i, cut ≤ i → ramGroup L P i = ⊥ := Classical.choose_spec (exists_termination L p P)
  have stable (a b : ℕ) (hab : a ≤ b) (ha : ∀ i, a ≤ i → ramGroup L P i = ⊥) :
      artinPartial L P ρ a = artinPartial L P ρ b := by
    have equality :
        (∑ j ∈ range a, ramCard L P (j+1) * fixedCodim L P ρ (j+1)) =
        (∑ j ∈ range b, ramCard L P (j+1) * fixedCodim L P ρ (j+1)) := by
      apply Finset.sum_subset (Finset.range_mono hab)
      intro j _ hj
      have hj' : a ≤ j := by simpa using hj
      simp [fixedCodim_eq_zero L P ρ (j+1) (ha _ (by omega))]
    simp only [artinPartial, equality]
  change artinPartial L P ρ cut = artinPartial L P ρ n
  rcases Nat.le_total cut n with h | h
  · exact stable cut n h hcut
  · exact (stable n cut h stops).symm

theorem artinConductor_le [FiniteDimensional k V] (ρ : Representation k (decompositionGroup L P) V) :
    artinConductor L p P ρ ≤ (Module.finrank k V : ℚ) *
      (1 + 2*(padicValNat p (P.ramificationIdx ℤ) : ℚ)) :=
  artinPartial_le L p P ρ _

#print axioms Sun28.SurfaceHeight.HilbertArtin.wild_different_le
#print axioms Sun28.SurfaceHeight.HilbertArtin.weighted_wild_le
#print axioms Sun28.SurfaceHeight.HilbertArtin.fixedCodim_eq_zero
#print axioms Sun28.SurfaceHeight.HilbertArtin.artinPartial_le

#print axioms Sun28.SurfaceHeight.HilbertArtin.exists_termination
#print axioms Sun28.SurfaceHeight.HilbertArtin.artinConductor_eq_of_termination
#print axioms Sun28.SurfaceHeight.HilbertArtin.artinConductor_le

end Sun28.SurfaceHeight.HilbertArtin
