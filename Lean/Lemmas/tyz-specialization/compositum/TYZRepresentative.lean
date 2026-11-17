import TYZCompositum

/-! The well-founded integral recursion in TYZ §3.1 and its field of definition. -/
namespace ZInQBlueprint.TYZ.Specialization
noncomputable section
attribute [local instance] Classical.decEq
open WeierstrassCurve.Affine

/-- Indices `d₁` for the printed sum with `n=d₀d₁` and `d₁>1`.
The factors `d₀` and `d₁` have their separate published residue conditions. -/
def recursionFactors (n : ℕ) : Finset ℕ := n.divisors.filter fun d₁ =>
  1 < d₁ ∧ (d₁%8=1 ∨ d₁%8=2 ∨ d₁%8=3) ∧
  ((n/d₁)%8=5 ∨ (n/d₁)%8=6 ∨ (n/d₁)%8=7)

private theorem cofactor_lt {n d₁ : ℕ} (h : d₁ ∈ recursionFactors n) : n/d₁ < n := by
  obtain ⟨hdiv,h1,_⟩ := Finset.mem_filter.mp h
  exact Nat.div_lt_self (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hdiv).2) h1

/-- The data named in the recursion: normalized genus traces, chosen signs of the
normalized L-values, and the four possible CM units of Theorem 3.3. -/
structure RecursionData where
  trace : ℕ → A
  L : ℕ → ℤ
  epsilon : ℕ → ℕ → GaussianUnit

/-- Hilbert class fields, modular images `z_n=f_n(P_n)`, and a finite choice
of lifts of the genus-class representatives in the absolute Galois group. -/
structure CMTraces where
  hilbert : ℕ → SubfieldQ
  modularPoint : ℕ → A
  lifts : ℕ → Finset Gal

/-- `H'_n = H_n(z_n)`. -/
def CMTraces.extended (S : CMTraces) (n : ℕ) : SubfieldQ := pointField (S.hilbert n) (S.modularPoint n)

/-- `Z(n)` as the finite sum of the chosen Galois conjugates on p. 739. -/
def CMTraces.trace (S : CMTraces) (n : ℕ) : A :=
  ∑ σ ∈ S.lifts n, sourceAction σ (S.modularPoint n)

def CMTraces.recursion (S : CMTraces) (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit) : RecursionData :=
  ⟨S.trace,L,eps⟩

theorem sourceAction_mem {F : SubfieldQ} (σ : Gal) (hF : ∀ x ∈ F, σ x ∈ F)
    {P : A} (hP : P ∈ pointsOver F) : sourceAction σ P ∈ pointsOver F := by
  cases P with
  | zero => simpa only [show Point.zero = (0:A) from rfl, map_zero] using (pointsOver F).zero_mem
  | some x y h =>
    obtain ⟨hx,hy⟩ := (some_mem_pointsOver F x y h).mp hP
    cases he : sourceAction σ (.some x y h) with
    | zero => exact (pointsOver F).zero_mem
    | some a b hab =>
      change Point.some (1^2 * σ x) (1^3 * σ y) _ = Point.some a b hab at he
      obtain ⟨ha,hb⟩ := Point.some.inj he
      simp only [one_pow,one_mul] at ha hb
      rw [some_mem_pointsOver,←ha,←hb]
      exact ⟨hF x hx,hF y hy⟩

/-- Each chosen lift acts inside `H'_n`, so its genus sum is defined there. -/
theorem CMTraces.trace_mem (S : CMTraces) (n : ℕ)
    (preserve : ∀ σ ∈ S.lifts n, ∀ x ∈ S.extended n, σ x ∈ S.extended n) :
    S.trace n ∈ pointsOver (S.extended n) := by
  apply (pointsOver (S.extended n)).sum_mem
  intro σ hσ
  exact sourceAction_mem σ (preserve σ hσ) ((pointField_le_iff _ _ _).mp le_rfl).2

/-- The actual point on the normalized source obtained from `Z` by the recursion. -/
def representative (D : RecursionData) (n : ℕ) : A :=
  D.trace n - ∑ d₁ ∈ (recursionFactors n).attach,
    (D.L d₁.val) • (D.epsilon (n/d₁.val) d₁.val).act (representative D (n/d₁.val))
termination_by n
decreasing_by exact cofactor_lt d₁.property

theorem representative_eq (D : RecursionData) (n : ℕ) :
    representative D n = D.trace n - ∑ d₁ ∈ recursionFactors n,
      (D.L d₁) • (D.epsilon (n/d₁) d₁).act (representative D (n/d₁)) := by
  rw [representative]
  rw [Finset.sum_attach (recursionFactors n) (fun t : ℕ =>
    (D.L t) • (D.epsilon (n/t) t).act (representative D (n/t)))]

/-- The residue-five and residue-six traces are defined over their indicated `H'`;
the residue-seven traces lie in `L_n(i)`, a consequence of their descent to `L_n`. -/
structure TraceFields (D : RecursionData) (H' : ℕ → SubfieldQ) : Prop where
  fiveSix : ∀ n, Squarefree n → n % 8 = 5 ∨ n % 8 = 6 → D.trace n ∈ pointsOver (H' n)
  seven : ∀ n, Squarefree n → n % 8 = 7 → D.trace n ∈ pointsOver (radicalField n)

private theorem trace_mem {D : RecursionData} {H' : ℕ → SubfieldQ} (fields : TraceFields D H')
    {n : ℕ} (hs : Squarefree n) (hmod : n%8=5 ∨ n%8=6 ∨ n%8=7) : D.trace n ∈ pointsOver (genusCompositum H' n) := by
  rcases hmod with h5|h6|h7
  · exact pointsOver_mono (classField_le_compositum (Nat.mem_divisors.mpr ⟨dvd_refl _,by omega⟩)
      (Or.inl h5) H') (fields.fiveSix n hs (Or.inl h5))
  · exact pointsOver_mono (classField_le_compositum (Nat.mem_divisors.mpr ⟨dvd_refl _,by omega⟩)
      (Or.inr h6) H') (fields.fiveSix n hs (Or.inr h6))
  · exact pointsOver_mono (show radicalField n ≤ genusCompositum H' n from le_sup_left) (fields.seven n hs h7)

/-- A single choice of traces and coefficients produces the representatives
for all divisors, and places them in the composita used in Lemma 3.18. -/
theorem representative_mem {D : RecursionData} {H' : ℕ → SubfieldQ} (fields : TraceFields D H')
    (n : ℕ) (hs : Squarefree n) (hmod : n%8=5 ∨ n%8=6 ∨ n%8=7) : representative D n ∈ pointsOver (genusCompositum H' n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [representative_eq]
    apply (pointsOver (genusCompositum H' n)).sub_mem (trace_mem fields hs hmod)
    apply (pointsOver (genusCompositum H' n)).sum_mem
    intro t ht
    obtain ⟨hdiv,_,_,hr⟩ := Finset.mem_filter.mp ht
    have hn := Nat.mem_divisors.mp hdiv
    apply (pointsOver (genusCompositum H' n)).zsmul_mem
    apply GaussianUnit.act_mem _ (i_mem_compositum H' n)
    exact pointsOver_mono (compositum_mono (Nat.div_dvd_of_dvd hn.1) hn.2 H') (ih _ (cofactor_lt ht) (hs.squarefree_of_dvd (Nat.div_dvd_of_dvd hn.1)) hr)

/-- Field-valued inputs from TYZ, now for the prescribed composite field
and the recursively specified point. The torsion statement quantifies over
only points with their coordinates in this field. -/
structure FieldInputs (D : RecursionData) (H' : ℕ → SubfieldQ) (d : ℕ) (hd : d%8=5) : Prop where
  torsion : ∀ Y : pointsOver (genusCompositum H' d), ∀ m : ℕ,
    0 < m → m • Y.val = 0 → (4:ℕ) • Y.val = 0
  anti : GaloisMinus d (tyzIsogeny ((2:ℕ) • representative D d))
  period : TraceAtTorsion hd (representative D d) (pointsOver (genusCompositum H' d))

/-- This constructor fixes both the ambient field and the representative in the rank theorem. -/
def traceData_of_fieldInputs {D : RecursionData} {H' : ℕ → SubfieldQ} (fields : TraceFields D H')
    {d : ℕ} {hd : d%8=5} (hs : Squarefree d) (h : FieldInputs D H' d hd) : TraceData d hd where
  fieldPoints := pointsOver (genusCompositum H' d)
  representative := ⟨representative D d, representative_mem fields d hs (Or.inl hd)⟩
  torsion_four := h.torsion
  double_minus := h.anti
  period := h.period

theorem publicRank_of_fieldInputs {D : RecursionData} {H' : ℕ → SubfieldQ} (fields : TraceFields D H')
    (h : ∀ d (hd : d%8=5), Squarefree d → FieldInputs D H' d hd) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk := by
  apply publicRank_of_traces
  exact fun d hd hs => ⟨traceData_of_fieldInputs fields hs (h d hd hs)⟩

/-- Starting from the Hilbert fields, modular images and lifts themselves.
The geometric class-seven trace descent is given on the actual sum. -/
theorem publicRank_of_cmTraces (S : CMTraces) (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit)
    (preserve : ∀ n, Squarefree n → n%8=5 ∨ n%8=6 → ∀ σ ∈ S.lifts n, ∀ x ∈ S.extended n, σ x ∈ S.extended n)
    (seven : ∀ n, Squarefree n → n%8=7 → S.trace n ∈ pointsOver (radicalField n))
    (h : ∀ d (hd : d%8=5), Squarefree d → FieldInputs (S.recursion L eps) S.extended d hd) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk :=
  publicRank_of_fieldInputs ⟨fun n hs hn => S.trace_mem n (preserve n hs hn), seven⟩ h

#print axioms CMTraces.trace_mem
#print axioms publicRank_of_cmTraces
#print axioms representative_eq
#print axioms representative_mem
#print axioms traceData_of_fieldInputs
#print axioms publicRank_of_fieldInputs
end
end ZInQBlueprint.TYZ.Specialization
