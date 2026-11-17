import IdealCount
import CountSelection

namespace Sun28.PrimeValues
open Finset Filter Topology Sun28.CutoffCount Sun28.SinglePrime Sun28.ContactFactors Sun28.FinitePattern Sun28.PrimeMass
open scoped Classical
noncomputable section

def classCount (A : Fin 3→ℚ) (d L N W : ℕ) : ℕ :=
  ∑ z ∈ (Ioc (N/2) N ×ˢ Icc 1 W).filter (fun z : ℕ×ℕ=>d∣z.2),idealTuples A L z

theorem eventual_class_count (A : Fin 3→ℚ) (d L : ℕ) :
    ∃ I : ℕ, ∀ j≥I, ∀ᶠ t : ℕ in atTop,
      let N:=lengthAt t
      let W:=rowWidth j N
      classCount A d L N W=2^(shifts A).card*count A d L N W := by
  obtain ⟨I,g⟩:=guard_rows A
  refine ⟨I,fun j large=>?_⟩
  filter_upwards [length_grows.eventually (g j large),
      length_grows.eventually (eventually_ge_atTop (4*(max L 7+1)))] with t guard late
  apply integer_box_multiplicity
  intro z mem i
  have gm:=guard z mem i
  have r : (4:ℝ)*((max L 7:ℕ)+1) ≤ lengthAt t := by exact_mod_cast late
  have pos : ((max L 7:ℕ):ℝ) < (form A z i:ℝ) := by linarith
  have intv : ((max L 7:ℕ):ℤ)<form A z i := by exact_mod_cast pos
  omega

/-- Counts of actual prime ideals, with the conjugacy multiplicity on the left
of the inequality. -/
def classRows (A : Fin 3→ℚ) (d L : ℕ) (δ : ℝ) : Prop :=
  ∀ J:ℕ, ∃j≥J, ∃ᶠ t:ℕ in atTop,
    let N:=lengthAt t
    let W:=rowWidth j N
    (2:ℝ)^(shifts A).card*(δ*((N:ℝ)*W)/(Real.log N)^(shifts A).card) ≤
      (classCount A d L N W:ℝ)

theorem rows_iff_classes (A : Fin 3→ℚ) (d L : ℕ) (δ : ℝ) :
    rows A d L δ ↔ classRows A d L δ := by
  have eq := eventual_class_count A d L
  obtain ⟨I,g⟩:=eq
  have equiv (j:ℕ) (large:I≤j) : ∀ᶠ t:ℕ in atTop,
      let N:=lengthAt t
      let W:=rowWidth j N
      let m:=δ*((N:ℝ)*W)/(Real.log N)^(shifts A).card
      (m≤(count A d L N W:ℝ)) ↔ (2:ℝ)^(shifts A).card*m≤(classCount A d L N W:ℝ) := by
    filter_upwards [g j large] with t h
    dsimp only at h ⊢
    rw [h,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    exact (mul_le_mul_iff_right₀ (by positivity)).symm
  constructor <;> intro H J
  · obtain ⟨j,hi,found⟩:=H (max I J)
    exact ⟨j,(le_max_right ..).trans hi,(found.and_eventually (equiv j ((le_max_left ..).trans hi))).mono
      fun _ h=>h.2.1 h.1⟩
  · obtain ⟨j,hi,found⟩:=H (max I J)
    exact ⟨j,(le_max_right ..).trans hi,(found.and_eventually (equiv j ((le_max_left ..).trans hi))).mono
      fun _ h=>h.2.2 h.1⟩

end
end Sun28.PrimeValues
#print axioms Sun28.PrimeValues.eventual_class_count
#print axioms Sun28.PrimeValues.rows_iff_classes
