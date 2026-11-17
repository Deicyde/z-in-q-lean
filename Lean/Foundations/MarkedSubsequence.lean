import OddMinimum

namespace MarkedSubsequence

private abbrev RecurrentSet := {P : Nat → Prop // OddMinimum.Often P}

/-- A bounded observable has a constant fibre inside any recurrent set of stages. -/
private theorem recurrent_fibre (s : RecurrentSet) (f : Nat → Nat) (r : Nat)
    (bounded : ∀ i, f i ≤ r) : ∃ c, OddMinimum.Often (fun i => s.val i ∧ f i = c) := by
  have hit : OddMinimum.Often (fun i => ∃ c, c ≤ r ∧ s.val i ∧ f i = c) := by
    intro start
    obtain ⟨i, hi, hmem⟩ := s.property start
    exact ⟨i, hi, f i, bounded i, hmem, rfl⟩
  obtain ⟨c, _, h⟩ := OddMinimum.bounded_pigeonhole (fun i c => s.val i ∧ f i = c) r hit
  exact ⟨c, h⟩

/-- For countably many observables, each with its own finite bound, there is one
strictly increasing sequence of stages. Its `k`-th observable is constant from
subsequence index `k` onwards. No compatibility between successive stages is assumed. -/
theorem bounded_observables_subsequence (value : Nat → Nat → Nat) (bound : Nat → Nat)
    (bounded : ∀ k i, value k i ≤ bound k) :
    ∃ stage : Nat → Nat, (∀ i j, i < j → stage i < stage j) ∧
      ∀ k n, k ≤ n → value k (stage n) = value k (stage k) := by
  classical
  let refine (k : Nat) (s : RecurrentSet) : RecurrentSet :=
    let h := recurrent_fibre s (value k) (bound k) (bounded k)
    ⟨fun i => s.val i ∧ value k i = Classical.choose h, Classical.choose_spec h⟩
  let allStages : RecurrentSet := ⟨fun _ => True, fun n => ⟨n, Nat.le_refl n, trivial⟩⟩
  let cells : Nat → RecurrentSet := Nat.rec allStages refine
  have previous (k i : Nat) (hi : (cells (k+1)).val i) : (cells k).val i := hi.1
  have same (k i j : Nat) (hi : (cells (k+1)).val i) (hj : (cells (k+1)).val j) :
      value k i = value k j := hi.2.trans hj.2.symm
  have nested {a b : Nat} (h : a ≤ b) (i : Nat) : (cells b).val i → (cells a).val i := by
    induction h with
    | refl => exact fun hi => hi
    | step h ih => exact fun hi => ih (previous _ i hi)
  let pick (k start : Nat) := Classical.choose ((cells (k+1)).property start)
  have picked (k start : Nat) : start ≤ pick k start ∧ (cells (k+1)).val (pick k start) :=
    Classical.choose_spec ((cells (k+1)).property start)
  let stage : Nat → Nat := Nat.rec (pick 0 0) (fun k prev => pick (k+1) (prev+1))
  have member (k : Nat) : (cells (k+1)).val (stage k) := by
    cases k with
    | zero => exact (picked 0 0).2
    | succ n => exact (picked (n+1) (stage n + 1)).2
  have grows (k : Nat) : stage k < stage (k+1) := (picked (k+1) (stage k + 1)).1
  refine ⟨stage, ?_, ?_⟩
  · intro i j hij
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases e : i = j
      · subst i; exact grows j
      · exact Nat.lt_trans (ih (by omega)) (grows j)
  · intro k n hkn
    exact same k (stage n) (stage k) (nested (Nat.succ_le_succ hkn) _ (member n)) (member k)

/-- Dependent finite color sets are allowed: the observable at mark `k` takes
values in `Fin (colors k)`. -/
theorem finite_observables_subsequence (colors : Nat → Nat)
    (value : (k : Nat) → Nat → Fin (colors k)) :
    ∃ stage : Nat → Nat, (∀ i j, i < j → stage i < stage j) ∧
      ∀ k n, k ≤ n → value k (stage n) = value k (stage k) := by
  obtain ⟨stage, hg, hv⟩ := bounded_observables_subsequence (fun k i => (value k i).val)
    colors (fun k i => Nat.le_of_lt (value k i).isLt)
  exact ⟨stage, hg, fun k n hkn => Fin.ext (hv k n hkn)⟩

/-- The color labels may be arbitrary dependent types. Only the observed values at
one mark must lie in a finite list; neither an enumeration nor decidable equality
on the ambient type is required as data. -/
theorem finite_range_subsequence {α : Nat → Type u} (value : (k : Nat) → Nat → α k)
    (finite : ∀ k, ∃ labels : List (α k), ∀ i, value k i ∈ labels) :
    ∃ stage : Nat → Nat, (∀ i j, i < j → stage i < stage j) ∧
      ∀ k n, k ≤ n → value k (stage n) = value k (stage k) := by
  classical
  let labels (k : Nat) := Classical.choose (finite k)
  have index (k i : Nat) : ∃ j : Fin (labels k).length, (labels k).get j = value k i := by
    obtain ⟨j, hj, he⟩ := List.getElem_of_mem (Classical.choose_spec (finite k) i)
    exact ⟨⟨j, hj⟩, he⟩
  let code (k i : Nat) := Classical.choose (index k i)
  have decode (k i : Nat) : (labels k).get (code k i) = value k i :=
    Classical.choose_spec (index k i)
  obtain ⟨stage, hg, hc⟩ := finite_observables_subsequence (fun k => (labels k).length) code
  refine ⟨stage, hg, ?_⟩
  intro k n hkn
  calc
    value k (stage n) = (labels k).get (code k (stage n)) := (decode k (stage n)).symm
    _ = (labels k).get (code k (stage k)) := congrArg (labels k).get (hc k n hkn)
    _ = value k (stage k) := decode k (stage k)

#print axioms bounded_observables_subsequence
#print axioms finite_observables_subsequence
#print axioms finite_range_subsequence

end MarkedSubsequence
