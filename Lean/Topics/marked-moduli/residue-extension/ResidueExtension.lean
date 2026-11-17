import Mathlib.FieldTheory.Finite.Extension
import ClusterCharts

/-! A single degree-twelve residue field for both collision charts. -/
noncomputable section
open Polynomial
namespace ZInQBlueprint.ResidueExtension

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Finite k] [CharP k p]

/-- If every positive degree up to d divides n, each polynomial of degree at most d
splits in the same prescribed finite field extension of degree n. -/
theorem splits_of_small_degree (d n : ℕ) [NeZero n]
    (hdiv : ∀ j, 0 < j → j ≤ d → j ∣ n) (f : k[X]) (hf : f.natDegree ≤ d) :
    (f.map (algebraMap k (FiniteField.Extension k p n))).Splits := by
  revert hf
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => simp
  | unit u hu => exact fun _ => hu.splits.map _
  | mul a i ha hi ih =>
    intro h
    rw [natDegree_mul hi.ne_zero ha] at h
    have hid : i.natDegree ∣ n := hdiv _ hi.natDegree_pos (by omega)
    have hirr := hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hid
    let g : k[X] := X ^ Nat.card k ^ n - X
    have hgs : (g.map (algebraMap k (FiniteField.Extension k p n))).Splits :=
      IsSplittingField.splits _ _
    have hgz : g ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ (NeZero.ne n) Finite.one_lt_card
    rw [Polynomial.map_mul]
    exact (hgs.of_dvd (map_ne_zero hgz) (map_dvd _ hirr)).mul (ih (by omega))

abbrev QuadraticField := FiniteField.Extension (ZMod p) p 2
instance : CharP (QuadraticField p) p :=
  charP_of_injective_algebraMap' (ZMod p) p

abbrev CommonField := FiniteField.Extension (QuadraticField p) p 6

theorem quadratic_degree : Module.finrank (ZMod p) (QuadraticField p) = 2 :=
  by simpa using FiniteField.finrank_zmod_extension (ZMod p) p 2

theorem common_degree : Module.finrank (ZMod p) (CommonField p) = 12 := by
  simpa [CommonField, quadratic_degree] using FiniteField.finrank_zmod_extension (QuadraticField p) p 6

theorem centres_split :
    (ClusterCharts.q₀ (X : (QuadraticField p)[X])).Splits ∧
    (ClusterCharts.qPole (X : (QuadraticField p)[X])).Splits := by
  have split2 (f : (ZMod p)[X]) (h : f.natDegree ≤ 2) :=
    splits_of_small_degree p (ZMod p) 2 2 (by intro j hj hj'; interval_cases j <;> decide) f h
  constructor
  · simpa [ClusterCharts.q₀] using split2 (ClusterCharts.q₀ X) (by unfold ClusterCharts.q₀; compute_degree)
  · simpa [ClusterCharts.qPole] using split2 (ClusterCharts.qPole X) (by unfold ClusterCharts.qPole; compute_degree)

/-- All base-field scalars acquire square roots in the same quadratic field. -/
theorem square_root (b : ZMod p) :
    ∃ a : QuadraticField p, a^2 = algebraMap (ZMod p) (QuadraticField p) b := by
  have split := splits_of_small_degree p (ZMod p) 2 2
    (by intro j hj hj'; interval_cases j <;> decide) (X^2 - C b) (by compute_degree)
  let e := algebraMap (ZMod p) (QuadraticField p)
  let e' := @algebraMap (ZMod p) (QuadraticField p) _ _
    (FiniteField.instAlgebraExtension (ZMod p) p 2)
  have h : (X^2 - C (e' b)).Splits := by simpa [e'] using split
  have he : e' = e := Subsingleton.elim _ _
  rw [he] at h
  obtain ⟨a, ha⟩ := h.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by
    rw [natDegree_X_pow_sub_C]; decide))
  exact ⟨a, by simpa [sub_eq_zero] using ha⟩

/-- The statement is uniform in the coefficients, hence in all choices of both centres and units. -/
theorem cubics_split (A B : QuadraticField p) :
    ((C A * X^3 + C B * X).map (algebraMap (QuadraticField p) (CommonField p))).Splits ∧
    ((C A * X^3 + C B).map (algebraMap (QuadraticField p) (CommonField p))).Splits := by
  have split3 (f : (QuadraticField p)[X]) (h : f.natDegree ≤ 3) :=
    splits_of_small_degree p (QuadraticField p) 3 6
      (by intro j hj hj'; interval_cases j <;> decide) f h
  constructor <;> apply split3 <;> compute_degree

end ZInQBlueprint.ResidueExtension
#print axioms ZInQBlueprint.ResidueExtension.splits_of_small_degree
#print axioms ZInQBlueprint.ResidueExtension.quadratic_degree
#print axioms ZInQBlueprint.ResidueExtension.common_degree
#print axioms ZInQBlueprint.ResidueExtension.centres_split
#print axioms ZInQBlueprint.ResidueExtension.square_root
#print axioms ZInQBlueprint.ResidueExtension.cubics_split
