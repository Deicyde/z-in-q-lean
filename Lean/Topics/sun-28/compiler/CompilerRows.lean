import RationalSamples
import TestsAtlas

/-! Build one row of the compiler from a projection b, a determinant
coefficient d, and one sample ℓ for the product of all input inequations. -/
open Polynomial ZInQBlueprint.SunTower ZInQBlueprint.SunResultant
open ZInQBlueprint.SunResultant.ParamTower Sun28.Branches
namespace Sun28.Compiler
noncomputable section
variable {m n : ℕ}
abbrev Test (m n : ℕ) := MvPolynomial (Fin n) (Poly m)

/-- Each earlier coefficient of each candidate must vanish. -/
def lowerTests (T : ParamTower (Poly m) n) (d : ℕ) : List (Polynomial (Poly m)) :=
  (List.range (bound T + 1)).flatMap fun j =>
    (List.range d).map fun k => C ((collision T j).coeff k)

/-- Sample numbers 0 through D for each input equation. -/
def equationTests (T : ParamTower (Poly m) n) (b : ℕ) (E : List (Test m n)) :
    List (Polynomial (Poly m)) :=
  E.flatMap fun f => (List.range (T.degreeProduct+1)).map fun j => sample T b j f

def row (T : ParamTower (Poly m) n) (E G : List (Test m n)) (b d ℓ : ℕ) :
    List (Chart m) :=
  testsAtlas (imagePolynomial T (linearForm (Poly m) n b))
    (lowerTests T d ++ equationTests T b E)
    [C ((collision T b).coeff d), sample T b ℓ G.prod]

private theorem constant_root (a : Poly m) (p : Fin m → ℚ) (t : ℚ) :
    ((C a).map (value p)).IsRoot t ↔ value p a=0 := by simp [IsRoot.def]

private theorem lowerTests_spec (T : ParamTower (Poly m) n) (d : ℕ)
    (p : Fin m → ℚ) (t : ℚ) :
    (∀ f ∈ lowerTests T d, (f.map (value p)).IsRoot t) ↔
    ∀ j ≤ bound T, ∀ k<d, value p ((collision T j).coeff k)=0 := by
  simp only [lowerTests,List.forall_mem_flatMap,List.forall_mem_map,List.mem_range,constant_root,
    Nat.lt_succ_iff]

private theorem equationTests_spec (T : ParamTower (Poly m) n) (b : ℕ)
    (E : List (Test m n)) (p : Fin m → ℚ) (t : ℚ) :
    (∀ f ∈ equationTests T b E, (f.map (value p)).IsRoot t) ↔
    ∀ f ∈ E, ∀ j ≤ T.degreeProduct, ((sample T b j f).map (value p)).IsRoot t := by
  simp only [equationTests,List.forall_mem_flatMap,List.forall_mem_map,List.mem_range,
    Nat.lt_succ_iff]

/-- Every root test in a selected row is made at the same rational number. -/
theorem row_spec (T : ParamTower (Poly m) n) (E G : List (Test m n)) (b d ℓ : ℕ)
    (p : Fin m → ℚ) :
    (∃ a ∈ row T E G b d ℓ, a.accepts p) ↔ Selected T (value p) b d ∧
      ∃ t : ℚ, ((imagePolynomial T (linearForm (Poly m) n b)).map (value p)).IsRoot t ∧
        (∀ f ∈ E, ∀ j ≤ T.degreeProduct, ((sample T b j f).map (value p)).IsRoot t) ∧
        ¬ ((sample T b ℓ G.prod).map (value p)).IsRoot t := by
  unfold row
  rw [testsAtlas_spec _ (imagePolynomial_monic T _) _ _ p]
  simp only [List.forall_mem_append,lowerTests_spec,equationTests_spec,List.forall_mem_cons,
    List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true,constant_root]
  unfold Selected
  constructor
  · rintro ⟨t,ht,⟨lo,eqs⟩,pos,ng⟩
    exact ⟨⟨pos,lo⟩,t,ht,eqs,ng⟩
  · rintro ⟨⟨pos,lo⟩,t,ht,eqs,ng⟩
    exact ⟨t,ht,⟨lo,eqs⟩,pos,ng⟩

/-- Multiplication encodes any finite conjunction of inequations. -/
theorem product_nonzero (φ : Poly m →+* ℚ) (x : Fin n → ℚ) (G : List (Test m n)) :
    MvPolynomial.eval₂Hom φ x G.prod ≠ 0 ↔ ∀ g ∈ G, MvPolynomial.eval₂Hom φ x g ≠ 0 := by
  induction G with
  | nil => simp
  | cons g gs ih => rw [List.prod_cons,map_mul,mul_ne_zero_iff,List.forall_mem_cons,ih]

#print axioms row_spec
#print axioms product_nonzero
end
end Sun28.Compiler
