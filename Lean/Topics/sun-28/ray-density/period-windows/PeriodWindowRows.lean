import PeriodSharedArms
import PeriodNarrow

namespace Sun28.PeriodWindows
open scoped Classical
open Sun28.FixedPreparation
open Sun28.QualitativeRows Sun28.ContactFactors Sun28.Forward Sun28.Ordinary Sun28.TwistRank

noncomputable def bothArms {ι : Type*} [Fintype ι] (o : ι→Bool→ℕ) (C : ℕ) : Finset ι :=
  Finset.univ.filter (fun i=>active o C i true ∧ active o C i false)

/-- A finite family can lose less than one two-arm position per row on average. -/
theorem point_of_few_active_positions {X : ℤ} {w : Window X} {L : ℕ} {I : Type*}
    (S : Finset I) (F : I→PeriodFrame w L)
    (loss : (∑ a∈S,(bothArms (F a).orders (Nat.factorial 576)).card) < S.card) : PointRow w := by
  classical
  by_contra bad
  have pos (a:I) : 1≤(bothArms (F a).orders (Nat.factorial 576)).card := by
    by_contra! h
    have empty:=Finset.card_eq_zero.mp (show _=0 by exact Nat.lt_one_iff.mp h)
    apply bad (point_row_of_one_arm (F a) ?_)
    intro i hb
    have mem : i∈bothArms (F a).orders (Nat.factorial 576) := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hb⟩
    rw [empty] at mem
    exact Finset.notMem_empty _ mem
  exact loss.not_ge (by simpa using Finset.sum_le_sum (s:=S) (fun a _=>pos a))

/-- One row per fixed integer and one preassigned real window. Arbitrarily many
primes are allowed across positions when both arms are not active at a position. -/
def ArmWindows {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Sun28.RealRatio.Orbit G) (model : Sun28.RealRatio.ParameterModel orbit) : Prop :=
  ∀ X : ℤ, ∃ F : PeriodFrame (fixedWindow orbit model X) 576,
    ∀ i, ¬(active F.orders (Nat.factorial 576) i true ∧ active F.orders (Nat.factorial 576) i false)

theorem rows_of_arm_windows {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (orbit : Sun28.RealRatio.Orbit G) (model : Sun28.RealRatio.ParameterModel orbit)
    (good : ArmWindows orbit model) (X : ℤ) : PointRow (fixedWindow orbit model X) := by
  obtain ⟨F,one⟩:=good X
  exact point_row_of_one_arm F one

end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.point_of_few_active_positions
#print axioms Sun28.PeriodWindows.rows_of_arm_windows
