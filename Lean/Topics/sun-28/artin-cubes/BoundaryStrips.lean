import TruncatedCells
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace Sun28.ArtinCube
open Set MeasureTheory
open scoped ENNReal
noncomputable section
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- Points whose representative in (0,1] belongs to the initial interval. -/
def strip (r : ℝ) : Set (AddCircle (1:ℝ)) :=
  (fun x : AddCircle (1:ℝ) => ((AddCircle.equivIoc (1:ℝ) 0 x : Set.Ioc 0 (0+1:ℝ)) : ℝ)) ⁻¹' Set.Ioc 0 r

theorem strip_measure (r : ℝ) (hr : r ≤ 1) :
    volume (strip r) = ENNReal.ofReal r := by
  have mp : MeasurePreserving
      (fun x : AddCircle (1:ℝ) => ((AddCircle.equivIoc (1:ℝ) 0 x : Set.Ioc 0 (0+1:ℝ)) : ℝ))
      volume (volume.restrict (Set.Ioc 0 (0+1:ℝ))) :=
    (measurePreserving_subtype_coe measurableSet_Ioc).comp (AddCircle.measurePreserving_equivIoc 1)
  rw [strip, mp.measure_preimage measurableSet_Ioc.nullMeasurableSet,
      Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.mpr, Real.volume_Ioc, sub_zero]
  exact Set.Ioc_subset_Ioc_right (by simpa using hr)

/-- For fixed step variables each translated forbidden interval has length R/n.
Union over the vertices bounds the discarded normalized volume. -/
theorem translated_strips {α : Type*} (I : Finset α) (shift : α → AddCircle (1:ℝ))
    (R n : ℝ) (hn : 0 < n) (hRn : R ≤ n) :
    volume (⋃ i ∈ I, (fun x => shift i + x) ⁻¹' strip (R/n)) ≤ I.card * ENNReal.ofReal (R/n) := by
  refine (measure_biUnion_finset_le _ _).trans ?_
  simp [measure_preimage_add, strip_measure _ ((div_le_one hn).mpr hRn)]

end
end Sun28.ArtinCube
#print axioms Sun28.ArtinCube.strip_measure
#print axioms Sun28.ArtinCube.translated_strips
