import AbelianPowers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The stable height of a factor and that of an isogenous power over one number field. -/
open AlgebraicGeometry CategoryTheory
open ZInQBlueprint.AbelianModel
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace ZOverQ.Qualitative.IsogenyHeight
noncomputable section
variable {M : Type} [Field M]

/-- In characteristic zero the degree of an isogeny is the number of geometric
points in its kernel. The test scheme is a geometric point of the base. -/
def kernelDegree {A B : GroupScheme M} (f : A ⟶ B) : ℕ :=
  let T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap M (AlgebraicClosure M))))
  Nat.card {x : T ⟶ A.X // x ≫ f.hom.hom.hom = 1}

/-- A finite surjective group homomorphism. -/
def IsIsogeny {A B : GroupScheme M} (f : A ⟶ B) : Prop :=
  IsFinite f.hom.hom.hom.left ∧ AlgebraicGeometry.Surjective f.hom.hom.hom.left

/-- Gaudron–Rémond, Théorème 1.4, with a fixed ground field and a finite
upper bound on dimension. The height used in the degree estimate belongs
to the source of the isogeny of small degree. -/
def DegreeBound (F : GroupScheme M → ℝ) (G : ℕ) : Prop :=
  ∃ (c : ℝ) (k : ℕ), 0 < c ∧ ∀ (X Y : GroupScheme M) (g : ℕ), 0 < g → g ≤ G →
    IsAbelianScheme X → IsAbelianScheme Y → SmoothOfRelativeDimension g X.X.hom →
    (∃ f : Y ⟶ X, IsIsogeny f) → ∃ f : X ⟶ Y, IsIsogeny f ∧
      0 < kernelDegree f ∧ (kernelDegree f : ℝ) ≤ c * (max 1 (F X))^k

/-- The absolute stable height is additive on products. Its change under an isogeny
is at most one half of the logarithm of its degree (von Känel, Lemma 3.2). -/
structure StableHeight (F : GroupScheme M → ℝ) : Prop where
  powers : ∀ (J : GroupScheme M), IsAbelianScheme J → ∀ n : ℕ,
    F (AbelianPowers.power J n) = ((n+1 : ℕ) : ℝ) * F J
  isogeny : ∀ {X Y : GroupScheme M}, IsAbelianScheme X → IsAbelianScheme Y →
    ∀ f : X ⟶ Y, IsIsogeny f → |F Y - F X| ≤ Real.log (kernelDegree f) / 2

/-- A single pair of constants works for every positive power of a Jacobian
isogenous to a variety of dimension at most G. Neither the degree of the
given isogeny nor the multiplicity is required to be bounded separately. -/
theorem uniform_power_bound (F : GroupScheme M → ℝ) (G : ℕ)
    (stable : StableHeight F) (gr : DegreeBound F G) :
    ∃ a b : ℝ, 0 ≤ a ∧ ∀ (B J : GroupScheme M) (g n : ℕ), 0 < g → g ≤ G →
      IsAbelianScheme B → IsAbelianScheme J → SmoothOfRelativeDimension g B.X.hom →
      (∃ f : AbelianPowers.power J n ⟶ B, IsIsogeny f) →
      max 1 (F J) ≤ a * max 1 (F B) + b := by
  obtain ⟨c,k,hc,small⟩ := gr
  refine ⟨1+(k:ℝ)/2, max 0 (Real.log c)/2, by positivity, ?_⟩
  intro B J g n hg hG hB hJ dim iso
  have hpow := AbelianPowers.abelian_power hJ n
  obtain ⟨f,hf,hd,degree⟩ := small B _ g hg hG hB hpow dim iso
  let H := max 1 (F B)
  have hH : 1 ≤ H := le_max_left _ _
  have pos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have logD := Real.log_le_log (by exact_mod_cast hd : 0 < (kernelDegree f : ℝ)) degree
  change Real.log (kernelDegree f) ≤ Real.log (c*H^k) at logD
  rw [Real.log_mul hc.ne' (pow_ne_zero _ pos.ne'),Real.log_pow] at logD
  have logH := Real.log_le_sub_one_of_pos pos
  have scaled := mul_le_mul_of_nonneg_left logH (Nat.cast_nonneg k (α:=ℝ))
  have shift := (le_abs_self _).trans (stable.isogeny hB hpow f hf)
  rw [stable.powers J hJ n] at shift
  have s₀ := le_max_right 0 (Real.log c)
  have s₁ := le_max_left 0 (Real.log c)
  have FB : F B ≤ H := le_max_right _ _
  change max 1 (F J) ≤ (1+(k:ℝ)/2)*H + max 0 (Real.log c)/2
  have kH := mul_nonneg (Nat.cast_nonneg k (α:=ℝ)) pos.le
  apply max_le
  · nlinarith
  · by_cases positive : 0 ≤ F J
    · have jH := mul_nonneg (Nat.cast_nonneg n (α:=ℝ)) positive
      push_cast at shift
      nlinarith
    · nlinarith

end
end ZOverQ.Qualitative.IsogenyHeight

#print axioms ZOverQ.Qualitative.IsogenyHeight.kernelDegree
#print axioms ZOverQ.Qualitative.IsogenyHeight.uniform_power_bound
