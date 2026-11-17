import TwistPoint
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-! Kummer descent on the fixed congruent-number curve. The unfinished
arithmetic steps have concrete domains and codomains. The proved theorem
below combines them by finite cardinality. -/
namespace ZInQBlueprint.Rank

noncomputable section
attribute [local instance] Classical.decEq

/-- Port of PR24's local 2-cover in the x-chart, including infinity. -/
def cover (K : Type*) [Field K] (d a b : K) : Prop :=
  (IsSquare a ∧ IsSquare b) ∨
    ∃ x : K, IsSquare (x / a) ∧ IsSquare ((x-d) / b) ∧ IsSquare ((x+d) / (a*b))

/-- Exact set of signed squarefree representatives of everywhere-locally
soluble 2-coverings, with the real and every p-adic place. -/
def selmer (d : ℕ) : Set (ℤ × ℤ) :=
  {ab | Squarefree ab.1 ∧ Squarefree ab.2 ∧ cover ℝ d ab.1 ab.2 ∧
    ∀ (p : ℕ) [Fact p.Prime], cover ℚ_[p] d ab.1 ab.2}

abbrev RationalPoint (d : ℕ) := (congruentCurve d).toAffine.Point

/-- Rational first and second Kummer coordinates with all three 2-torsion charts. -/
def kummer (d : ℕ) : RationalPoint d → ℚ × ℚ
  | .zero => (1, 1)
  | @WeierstrassCurve.Affine.Point.some _ _ _ x _ _ =>
    if x = 0 then (-1, -(d:ℚ)) else if x = d then (d, 2)
    else if x = -(d:ℚ) then (-(d:ℚ), -2*(d:ℚ)) else (x, x-d)

def sameSquareclass (x y : ℚ) : Prop := ∃ r : ℚ, r ≠ 0 ∧ x=y*r^2

def represents (d : ℕ) (P : RationalPoint d) (ab : ℤ × ℤ) : Prop :=
  sameSquareclass ab.1 (kummer d P).1 ∧ sameSquareclass ab.2 (kummer d P).2

def doubles (G : Type*) [AddCommGroup G] : AddSubgroup G where
  carrier := Set.range (fun x : G => (2:ℕ) • x)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩; exact ⟨x+y, by simp⟩
  neg_mem' := by rintro _ ⟨x,rfl⟩; exact ⟨-x, by simp⟩

abbrev modTwo (d : ℕ) := RationalPoint d ⧸ doubles (RationalPoint d)

/-- The classical injective Kummer map, with coordinates prescribed on every
representative. This is a construction obligation, with no axiom declaration. -/
structure KummerEmbedding (d : ℕ) where
  toSelmer : modTwo d ↪ {ab : ℤ × ℤ // ab ∈ selmer d}
  onPoint (P : RationalPoint d) :
    represents d P (toSelmer (QuotientAddGroup.mk P)).1

/-- Consequence of Mordell–Weil, rank ≥1, and four rational 2-torsion points.
The quotient is the actual point group modulo its doubles. -/
def EightModTwoOfPositiveRank : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → PositiveRank d → Nonempty (Fin 8 ↪ modTwo d)

/-- Rational instance of the explicit point/cover equivalence upstream.
The port needs only the implication from a represented class to a cover. -/
def CoverOfKummerCoordinates : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (P : RationalPoint d) (ab : ℤ × ℤ),
    ab ∈ selmer d → represents d P ab → cover ℚ d ab.1 ab.2

/-- The genus comparison and geometric genus-point step supply positive rank.
Only the eight-element Selmer assumption is needed to realize *every* cover. -/
theorem allCoversOfRow (d : ℕ) (hd : d % 8=5) (hs : Squarefree d)
    (comparison : DeterminantGenusComparison) (tyz : TYZGenusToAntiPoint)
    (descend : NegativeTwistDescent) (eight : EightModTwoOfPositiveRank)
    (embedding : KummerEmbedding d) (pointCover : CoverOfKummerCoordinates)
    (hsize : (selmer d).ncard=8) (row : (smithM5b d).det=1) :
    ∀ ab ∈ selmer d, cover ℚ d ab.1 ab.2 := by
  obtain ⟨j⟩ := eight d hd hs (positiveRank_of_row hd hs comparison tyz descend row)
  let f : Fin 8 → ℤ × ℤ := fun i => (embedding.toSelmer (j i)).1
  have hinj : Function.Injective f :=
    Subtype.val_injective.comp (embedding.toSelmer.injective.comp j.injective)
  have hsub : Set.range f ⊆ selmer d := by
    rintro _ ⟨i,rfl⟩
    exact (embedding.toSelmer (j i)).2
  have hcard : (Set.range f).ncard=8 := by simp [Set.ncard_range_of_injective hinj]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.finite_of_ncard_pos (by omega))
  intro ab hab
  rw [←heq] at hab
  obtain ⟨i,rfl⟩ := hab
  obtain ⟨P, hP⟩ := QuotientAddGroup.mk_surjective (j i)
  have hc := embedding.onPoint P
  rw [hP] at hc
  exact pointCover d (by omega) P _ (embedding.toSelmer (j i)).2 hc

end
end ZInQBlueprint.Rank

#print axioms ZInQBlueprint.Rank.allCoversOfRow
