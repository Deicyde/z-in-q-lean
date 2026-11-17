import CompatibleCongruences
import ParityTransport
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

namespace Sun28.QualitativeRows

/-- Moduli and literal comparison residues for fixed conditions and the
two reductions at a selected prime. True is the side assigned to h−anchor. -/
def comparisonMod {ι J : Type*} (order : ι → Bool → ℕ) (m : J → ℕ) :
    J ⊕ (ι × Bool) → ℕ
  | .inl j => m j
  | .inr (i,s) => order i s

def comparisonRes {ι J : Type*} (C : ℕ) (r : J → ℕ) (x : ι → Bool) :
    J ⊕ (ι × Bool) → ℕ
  | .inl j => r j
  | .inr (i,s) => if (s ^^ x i) then C else 0

/-- The fixed vertex is the sentinel for absolute orientation choices.
Repeated constraints, parallel edges, and an incompatible single choice are retained. -/
inductive Constraint {ι J : Type*} (order : ι → Bool → ℕ) (m r : J → ℕ) (C : ℕ) :
    Option ι → Option ι → Bool → Prop where
  | pair (i j : ι) (s t : Bool) (bad : ¬(order i s).gcd (order j t) ∣ C) :
    Constraint order m r C (some i) (some j) (s ^^ t)
  | pin (j : J) (i : ι) (s : Bool) (t : Bool)
      (bad : ¬r j ≡ (if t then C else 0) [MOD (m j).gcd (order i s)]) :
    Constraint order m r C none (some i) (!(s ^^ t))

def Edge {ι J : Type*} (order : ι → Bool → ℕ) (m r : J → ℕ) (C : ℕ)
    (u v : Option ι) (d : Bool) : Prop :=
  Constraint order m r C u v d ∨ Constraint order m r C v u d

theorem edge_symm {ι J : Type*} {order : ι → Bool → ℕ} {m r : J → ℕ} {C : ℕ}
    {u v : Option ι} {d : Bool} (h : Edge order m r C u v d) :
    Edge order m r C v u d := h.elim Or.inr Or.inl

private theorem two_res (C g : ℕ) (s t : Bool) :
    ((if s then C else 0) ≡ (if t then C else 0) [MOD g]) ↔ s=t ∨ g∣C := by
  cases s <;> cases t
  · exact ⟨fun _ => Or.inl rfl,fun _ => rfl⟩
  · exact ⟨fun eq => Or.inr (Nat.modEq_zero_iff_dvd.mp eq.symm),
      fun h => h.elim (fun bad => Bool.noConfusion bad) (fun dvd => (Nat.modEq_zero_iff_dvd.mpr dvd).symm)⟩
  · exact ⟨fun eq => Or.inr (Nat.modEq_zero_iff_dvd.mp eq),
      fun h => h.elim (fun bad => Bool.noConfusion bad) Nat.modEq_zero_iff_dvd.mpr⟩
  · exact ⟨fun _ => Or.inl rfl,fun _ => rfl⟩

private theorem xor_equal (a b s t : Bool) : (a ^^ b) = (s ^^ t) ↔ (s ^^ a) = (t ^^ b) := by
  cases a <;> cases b <;> cases s <;> cases t <;> decide

private theorem pin_iff (x s t : Bool) : x = !(s ^^ t) ↔ (s ^^ x) ≠ t := by
  cases x <;> cases s <;> cases t <;> decide

/-- Pairwise compatibility of all congruences, with the orientation assignment
fixed. The sentinel is assigned false. -/
theorem edge_iff {ι J : Type*} (order : ι → Bool → ℕ) (m r : J → ℕ) (C : ℕ) (x : ι → Bool)
    (base : ∀ i j, r i ≡ r j [MOD (m i).gcd (m j)]) :
    (∀ {u v d}, Edge order m r C u v d →
      ((u.elim false x) ^^ (v.elim false x)) = d) ↔
    ∀ i j, comparisonRes C r x i ≡ comparisonRes C r x j
      [MOD (comparisonMod order m i).gcd (comparisonMod order m j)] := by
  constructor
  · intro colors i j
    have fixed (j : J) (i : ι) (s : Bool) :
        r j ≡ (if s ^^ x i then C else 0) [MOD (m j).gcd (order i s)] := by
      by_contra bad
      have cc := colors (Or.inl (Constraint.pin j i s (s ^^ x i) bad))
      have k : x i = !(s ^^ (s ^^ x i)) := by
        change (false ^^ x i) = _ at cc
        exact (Bool.false_xor _).symm.trans cc
      exact (pin_iff (x i) s (s ^^ x i)).mp k rfl
    rcases i with i | ⟨i,s⟩ <;> rcases j with j | ⟨j,t⟩
    · exact base i j
    · exact fixed i j t
    · simpa only [comparisonMod,comparisonRes,Nat.gcd_comm (order i s) (m j)] using (fixed j i s).symm
    · apply (two_res ..).mpr
      by_cases d : (order i s).gcd (order j t)∣C
      · exact Or.inr d
      · have edge := colors (Or.inl (Constraint.pair i j s t d))
        exact Or.inl ((xor_equal ..).mp edge)
  · intro comp u v d e
    have direct {u v d} (c : Constraint order m r C u v d) :
        ((u.elim false x) ^^ (v.elim false x)) = d := by
      cases c with
      | pair i j s t bad =>
        obtain eq | good := (two_res ..).mp (comp (.inr (i,s)) (.inr (j,t)))
        · exact (xor_equal ..).mpr eq
        · exact (bad good).elim
      | pin j i s t bad =>
        have valid := comp (.inl j) (.inr (i,s))
        have ne : (s ^^ x i) ≠ t := by
          intro same
          apply bad
          simpa only [comparisonRes,comparisonMod,same] using valid
        simpa using (pin_iff (x i) s t).mpr ne
    rcases e with h | h
    · exact direct h
    · rw [Bool.xor_comm]; exact direct h

/-- An unbalanced cycle is the exact obstruction to choosing the Gaussian roots
and a single infinite progression for both anchors and all fixed residues. -/
theorem graph_criterion {ι J : Type*} [Fintype ι] [Fintype J]
    (order : ι → Bool → ℕ) (m r : J → ℕ) (C : ℕ)
    (nz : ∀ i s, 0 < order i s) (nz' : ∀ j, 0 < m j)
    (base : ∀ i j, r i ≡ r j [MOD (m i).gcd (m j)]) :
    (∀ v, ¬Walk (Edge order m r C) v v true) ↔
    ∃ (x : ι → Bool) (h : ℤ) (step : ℕ), 0<step ∧ ∀ k : ℤ, ∀ i,
      h + (step:ℤ)*k ≡ (comparisonRes C r x i : ℤ) [ZMOD (comparisonMod order m i : ℤ)] := by
  classical
  have positive (i : J ⊕ (ι × Bool)) : 0 < comparisonMod order m i := by
    cases i with
    | inl j => exact nz' j
    | inr i => exact nz i.1 i.2
  constructor
  · intro balanced
    obtain ⟨g, valid⟩ := (balanced_iff (Edge order m r C) (fun h => edge_symm h)).mpr balanced
    let x := fun i => g none ^^ g (some i)
    have normalized (v : Option ι) : v.elim false x = (g none ^^ g v) := by
      cases v <;> simp [x]
    have colors {u v d} (h : Edge order m r C u v d) :
        ((u.elim false x) ^^ (v.elim false x)) = d := by
      rw [normalized,normalized,←valid h]
      cases g none <;> cases g u <;> cases g v <;> decide
    obtain ⟨h, step, pos, all⟩ := CRT.solve Finset.univ (comparisonMod order m) (comparisonRes C r x)
      (fun i _ => positive i) (fun i _ j _ => (edge_iff order m r C x base).mp (@colors) i j)
    exact ⟨x,h,step,pos,fun k i => all k i (Finset.mem_univ _)⟩
  · rintro ⟨x,h,step,pos,all⟩
    have comp := (CRT.exists_iff Finset.univ (comparisonMod order m) (comparisonRes C r x)
      (fun i _ => positive i)).mp ⟨h,fun i _ => by simpa using all 0 i⟩
    have colors {u v d} (e : Edge order m r C u v d) := (edge_iff order m r C x base).mpr (fun i j => comp i (Finset.mem_univ _) j (Finset.mem_univ _)) e
    exact (balanced_iff (Edge order m r C) (fun h => edge_symm h)).mp
      ⟨fun v => v.elim false x,fun h => colors h⟩

end Sun28.QualitativeRows

#print axioms Sun28.QualitativeRows.edge_symm
#print axioms Sun28.QualitativeRows.edge_iff
#print axioms Sun28.QualitativeRows.graph_criterion
