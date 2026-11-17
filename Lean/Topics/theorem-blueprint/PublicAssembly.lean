import KummerCover
import RationalSelmer
import RootHeight
import LiteralV15
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Public definitions at 6f20b15, re-elaborated under the private toolchain.
The two separate public lemmas occur explicitly in the assembly theorem. -/
namespace ZInQBlueprint.PublicText
noncomputable section
open Classical Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

-- Public definition ZInQKernel/Target.lean#FrozenTarget
def FrozenTarget : Prop :=
  ∃ P : MvPolynomial (Fin 292890231905) Int,
    P.totalDegree < hyperoperation 4 2 7 ∧
    (∀ m : Fin 292890231905 →₀ Nat,
      (P.coeff m).natAbs < hyperoperation 4 2 8) ∧
    ∀ q : Rat,
      (∃ w : Fin 292890231904 → Rat,
        MvPolynomial.eval₂ (Int.castRingHom Rat) (Fin.cons q w) P = 0) ↔
      ∃ z : Int, (z : Rat) = q

-- Public definition ZInQKernel/RouteK/Selmer/Covering.lean#Loc
def Loc (K : Type*) [Field K] (d a b : K) : Prop :=
  (IsSquare a ∧ IsSquare b) ∨
    ∃ x : K, IsSquare (x / a) ∧ IsSquare ((x - d) / b) ∧ IsSquare ((x + d) / (a * b))

-- Public definition ZInQKernel/RouteK/Selmer/Covering.lean#Sel2
def Sel2 (d : ℕ) : Set (ℤ × ℤ) :=
  {ab | Squarefree ab.1 ∧ Squarefree ab.2 ∧ Loc ℝ d ab.1 ab.2 ∧
    ∀ (p : ℕ) [Fact p.Prime], Loc ℚ_[p] d ab.1 ab.2}

-- Public definition ZInQKernel/RouteK/Selmer/Covering.lean#CertifiedRankSel
def CertifiedRankSel : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 →
    (∃ ab ∈ Sel2 d, ab.1.natAbs % 8 = 7) → ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2

-- Public definition ZInQKernel/RouteK/Slots/Symbols.lean#legBit
noncomputable def legBit (p : ℕ) (a : ℤ) : ZMod 2 := if IsSquare (a : ZMod p) then 0 else 1

-- Public definition ZInQKernel/RouteK/Slots/Symbols.lean#lamBit
noncomputable def lamBit (p : ℕ) : ZMod 2 := legBit p (-1)

-- Public definition ZInQKernel/RouteK/Slots/Symbols.lean#muBit
noncomputable def muBit (p : ℕ) : ZMod 2 := legBit p 2

-- Public definition ZInQKernel/RouteK/Rank5b/Bordered.lean#border
def border {R : Type*} [Zero R] (M : Matrix ι ι R) (v : ι → R) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  Matrix.fromBlocks M (replicateCol Unit v) (replicateRow Unit v) 0

-- Public definition ZInQKernel/RouteK/Rank5b/Matrices.lean#aBit
noncomputable def aBit (d : ℕ) (i j : d.primeFactors) : ZMod 2 := legBit (i : ℕ) ((j : ℕ) : ℤ)

-- Public definition ZInQKernel/RouteK/Rank5b/Matrices.lean#yBit
noncomputable def yBit (d : ℕ) (i : d.primeFactors) : ZMod 2 := lamBit (i : ℕ)

-- Public definition ZInQKernel/RouteK/Rank5b/Matrices.lean#zBit
noncomputable def zBit (d : ℕ) (i : d.primeFactors) : ZMod 2 := muBit (i : ℕ)

-- Public definition ZInQKernel/RouteK/Rank5b/Matrices.lean#Lmat
noncomputable def Lmat (d : ℕ) : Matrix d.primeFactors d.primeFactors (ZMod 2) := fun i j =>
  if i = j then ∑ k ∈ Finset.univ.erase i, aBit d i k else aBit d i j

-- Public definition ZInQKernel/RouteK/Rank5b/Matrices.lean#M1
noncomputable def M1 (d : ℕ) :
    Matrix (d.primeFactors ⊕ d.primeFactors) (d.primeFactors ⊕ d.primeFactors) (ZMod 2) :=
  fromBlocks (Lmat d + (Lmat d)ᵀ) (Lmat d)ᵀ (Lmat d) (diagonal (zBit d))

-- Public definition ZInQKernel/RouteK/Rank5b/Matrices.lean#M5b
noncomputable def M5b (d : ℕ) :
    Matrix ((d.primeFactors ⊕ d.primeFactors) ⊕ Unit)
      ((d.primeFactors ⊕ d.primeFactors) ⊕ Unit) (ZMod 2) :=
  border (M1 d) (Sum.elim 0 (yBit d))

-- Public definition ZInQKernel/Hypotheses/Height.lean#ratHeight
noncomputable def ratHeight (u : ℚ) : ℝ :=
  Real.log (max |(u.num : ℝ)| (u.den : ℝ))

-- Public definition ZInQKernel/Hypotheses/Height.lean#contactSet
def contactSet : Finset ℚ := {0, -15, -20, -24, -30, -60}

-- Public definition ZInQKernel/Hypotheses/Height.lean#contactSupport
noncomputable def contactSupport (S : Finset ℕ) (u : ℚ) : ℕ :=
  ∏ p ∈ (∏ c ∈ contactSet, (u - c).num.natAbs).primeFactors with
      p ∉ S ∧ ∃ c ∈ contactSet, 0 < padicValRat p (u - c) ∧ Odd (padicValRat p (u - c)),
    p

-- Public definition ZInQKernel/Hypotheses/Height.lean#heightF0
noncomputable def heightF0 : ℕ := Nat.factorial 324

-- Public definition ZInQKernel/Hypotheses/Height.lean#heightD
noncomputable def heightD : ℕ := heightF0 * 3 ^ (256 * heightF0 ^ 4)

-- Public definition ZInQKernel/Hypotheses/Height.lean#heightG0
def heightG0 : ℕ := 116064000000

-- Public definition ZInQKernel/Hypotheses/Height.lean#heightE0
noncomputable def heightE0 : ℕ := 10 * (heightD * heightG0) ^ 2

-- Public definition ZInQKernel/Hypotheses/Height.lean#heightBcm
noncomputable def heightBcm : ℕ := heightD ^ 2 * 3 ^ (21000 * heightD ^ 2) + 1

-- Public definition ZInQKernel/Hypotheses/Height.lean#heightCcm
noncomputable def heightCcm : ℕ := 2 * heightBcm + 4096 * (1028 + 5 * heightD + 84000 * heightD ^ 2)

-- Public definition ZInQKernel/Hypotheses/Height.lean#heightQ
noncomputable def heightQ (R : ℝ) : ℝ := R ^ (R * heightE0)

-- Public definition ZInQKernel/Hypotheses/Height.lean#heightH6
noncomputable def heightH6 (R : ℝ) : ℝ :=
  2 * 10 ^ 13 * max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- The public assembly specializes S to Mult.S_mul. -/
def HeightInstance (S : Finset ℕ) : Prop := ∀ u : ℚ, u ∉ contactSet →
  ratHeight u ≤ heightH6 (heightD : ℝ) * (contactSupport S u : ℝ)^24

def GeometricComparisons (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet → ∃ stable theta : ℝ,
    ratHeight (SixContact.J u) ≤ 40*theta+22 ∧
    theta ≤ (10000*2^24)*max 1 stable ∧
    max 1 stable ≤ max 1 (max (heightCcm:ℝ) (heightQ (heightD:ℝ)^17)) *
      (contactSupport S u : ℝ)^24

theorem same_support (S : Finset ℕ) (u : ℚ) : contactSupport S u = SixContact.support S u := by
  classical
  rfl

theorem height_of_comparisons {S : Finset ℕ} (h : GeometricComparisons S) : HeightInstance S := by
  intro u hu
  obtain ⟨stable,theta,h₁,h₂,h₃⟩ := h u hu
  rw [same_support] at h₃ ⊢
  exact SixContact.contact_bound_of_heights h₁ h₂ h₃

theorem same_matrix (d : ℕ) : M5b d = Rank.smithM5b d := by
  classical
  rfl

theorem same_selmer (d : ℕ) : Sel2 d = Rank.selmer d := rfl
theorem same_frozen : FrozenTarget ↔ ManuscriptV15.Frozen := Iff.rfl
theorem same_certified_rank : CertifiedRankSel ↔ Descent.CertifiedRankSel := Iff.rfl

/-- Row 5b, Corollary 4.4 with its signed class. -/
def MatrixTest : Prop := ∀ {d : ℕ}, d % 8 = 5 → Squarefree d → (Sel2 d).ncard=8 →
  ∀ {ab : ℤ × ℤ}, ab ∈ Sel2 d → ab.1.natAbs%8=7 → (M5b d).det=1

theorem rank_of_four (row : MatrixTest) (genus : Rank.DeterminantGenusComparison)
    (point : Rank.TYZGenusToAntiPoint) (eight : Rank.EightModTwoOfPositiveRank)
    (embedding : ∀ d : ℕ, d % 8 = 5 → Squarefree d → Rank.KummerEmbedding d) :
    CertifiedRankSel := by
  intro d hd hs size witness
  obtain ⟨ab,hab,h7⟩ := witness
  have det := row hd hs size hab h7
  rw [same_matrix] at det
  exact Rank.allCoversOfCertifiedRow d hd hs genus point eight (embedding d hd hs) size det

/-- The first two arguments come from the separate public build. -/
theorem frozen_of_geometry_and_genus {S : Finset ℕ}
    (assemble : HeightInstance S → CertifiedRankSel → FrozenTarget) (row : MatrixTest)
    (geometry : GeometricComparisons S) (genus : Rank.DeterminantGenusComparison)
    (point : Rank.TYZGenusToAntiPoint) (eight : Rank.EightModTwoOfPositiveRank)
    (embedding : ∀ d : ℕ, d % 8 = 5 → Squarefree d → Rank.KummerEmbedding d) :
    FrozenTarget :=
  assemble (height_of_comparisons geometry) (rank_of_four row genus point eight embedding)

#print axioms same_support
#print axioms height_of_comparisons
#print axioms same_matrix
#print axioms same_selmer
#print axioms same_frozen
#print axioms same_certified_rank
#print axioms rank_of_four
#print axioms frozen_of_geometry_and_genus
end
end ZInQBlueprint.PublicText
