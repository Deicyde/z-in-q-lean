import ResultantProduct
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! An actual univariate polynomial over the parameter ring for the image of a tower. -/
open Polynomial
namespace ZInQBlueprint.SunResultant.ParamTower
noncomputable section
variable {R S L : Type*} [CommRing R] [CommRing S] [Field L]

/-- Apply θ to the parameters in every step of the tower. -/
def baseChange (θ : R →+* S) : {n : ℕ} → ParamTower R n → ParamTower S n
  | _, .base => .base
  | _, .adjoin T f hf => .adjoin (baseChange θ T) (f.map (MvPolynomial.map θ)) (hf.map _)

theorem satisfies_baseChange (θ : R →+* S) (φ : S →+* L) {n : ℕ}
    (T : ParamTower R n) (x : Fin n → L) :
    Satisfies φ (baseChange θ T) x ↔ Satisfies (φ.comp θ) T x := by
  induction T with
  | base => rfl
  | @adjoin n T f hf ih =>
    simp only [baseChange,Satisfies,Polynomial.map_map,ih]
    have h : (MvPolynomial.eval₂Hom φ (Fin.tail x)).comp (MvPolynomial.map θ) =
        MvPolynomial.eval₂Hom (φ.comp θ) (Fin.tail x) := by
      apply RingHom.ext
      intro g
      exact MvPolynomial.eval₂Hom_map_hom θ _ φ g
    rw [h]

/-- Root multiplicities are unchanged by a base change followed by specialization. -/
theorem rootTuples_baseChange (θ : R →+* S) (φ : S →+* L) {n : ℕ} (T : ParamTower R n) :
    rootTuples φ (baseChange θ T) = rootTuples (φ.comp θ) T := by
  induction T with
  | base => rfl
  | @adjoin n T f hf ih =>
    simp only [baseChange,rootTuples,ih]
    congr 1
    funext x
    have h : (MvPolynomial.eval₂Hom φ x).comp (MvPolynomial.map θ) =
        MvPolynomial.eval₂Hom (φ.comp θ) x := by
      apply RingHom.ext
      intro g
      exact MvPolynomial.eval₂Hom_map_hom θ _ φ g
    rw [Polynomial.map_map,h]

/-- Eliminate T−g(x) over R[T]. The resulting univariate polynomial has coefficients in R. -/
def imagePolynomial {n : ℕ} (T : ParamTower R n) (g : MvPolynomial (Fin n) R) : R[X] :=
  elim (baseChange (Polynomial.C : R →+* R[X]) T)
    (MvPolynomial.C Polynomial.X - MvPolynomial.map Polynomial.C g)

/-- For every specialization and every z in its algebraic closure, the root condition represents
exactly the geometric image of g on the given tower. The polynomial is chosen before φ and z. -/
theorem imagePolynomial_isRoot_iff [IsAlgClosed L] {n : ℕ} (T : ParamTower R n)
    (g : MvPolynomial (Fin n) R) (φ : R →+* L) (z : L) :
    ((imagePolynomial T g).map φ).IsRoot z ↔
      ∃ x : Fin n → L, Satisfies φ T x ∧ MvPolynomial.eval₂Hom φ x g = z := by
  let ρ : R[X] →+* L := Polynomial.eval₂RingHom φ z
  have hρ : ρ.comp Polynomial.C = φ := by ext r; simp [ρ]
  rw [IsRoot.def,Polynomial.eval_map]
  change ρ (elim _ _) = 0 ↔ _
  rw [elim_zero_iff]
  apply exists_congr
  intro x
  rw [satisfies_baseChange,hρ]
  apply and_congr_right
  intro hx
  rw [map_sub,MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_map_hom,hρ]
  simp [ρ,sub_eq_zero,eq_comm]

/-- The literal parameter polynomial has exactly the expected product values, with
multiplicities, for every choice of parameters and every target value. -/
theorem imagePolynomial_eval_product [IsAlgClosed L] {n : ℕ} (T : ParamTower R n)
    (g : MvPolynomial (Fin n) R) (φ : R →+* L) (z : L) :
    ((imagePolynomial T g).map φ).eval z =
      ((rootTuples φ T).map fun x => z - MvPolynomial.eval₂Hom φ x g).prod := by
  let ρ : R[X] →+* L := Polynomial.eval₂RingHom φ z
  have hρ : ρ.comp Polynomial.C = φ := by ext r; simp [ρ]
  rw [Polynomial.eval_map]
  change ρ (elim _ _) = _
  rw [elim_product,rootTuples_baseChange,hρ]
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  rw [map_sub,MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_map_hom,hρ]
  simp [ρ]


/-- Equality in the target polynomial ring with the product of linear factors, including
their multiplicities. This avoids a separate theorem about a regular representation. -/
theorem imagePolynomial_map [IsAlgClosed L] [Infinite L] {n : ℕ} (T : ParamTower R n)
    (g : MvPolynomial (Fin n) R) (φ : R →+* L) :
    (imagePolynomial T g).map φ =
      ((rootTuples φ T).map fun x => X-C (MvPolynomial.eval₂Hom φ x g)).prod := by
  apply Polynomial.funext
  intro z
  rw [imagePolynomial_eval_product,eval_multiset_prod,Multiset.map_map]
  simp [Function.comp_def]


/-- Multiplicities make the image degree constant under all specializations, even where
distinct projected values collide. -/
theorem imagePolynomial_degree [IsAlgClosed L] [Infinite L] {n : ℕ} (T : ParamTower R n)
    (g : MvPolynomial (Fin n) R) (φ : R →+* L) :
    ((imagePolynomial T g).map φ).natDegree = T.degreeProduct := by
  rw [imagePolynomial_map]
  let V := (rootTuples φ T).map fun x => MvPolynomial.eval₂Hom φ x g
  have h : (rootTuples φ T).map (fun x => X-C (MvPolynomial.eval₂Hom φ x g)) = V.map (X-C ·) := by
    simp [V,Multiset.map_map]
  rw [h,natDegree_multiset_prod_X_sub_C_eq_card,Multiset.card_map,card_rootTuples]


/-- Over a domain the literal image polynomial is monic already over the parameter ring.
Inject it into the algebraic closure of its fraction field to read its linear factors. -/
theorem imagePolynomial_monic [IsDomain R] {n : ℕ} (T : ParamTower R n)
    (g : MvPolynomial (Fin n) R) : (imagePolynomial T g).Monic := by
  let F := FractionRing R
  let K := AlgebraicClosure F
  let φ := (algebraMap F K).comp (algebraMap R F)
  have hi : Function.Injective φ :=
    (algebraMap F K).injective.comp (IsFractionRing.injective R F)
  apply Polynomial.monic_of_injective hi
  rw [imagePolynomial_map]
  exact monic_multiset_prod_of_monic _ _ (fun x _ => monic_X_sub_C _)

/-- The degree over the parameter domain equals the product of the monic stage degrees. -/
theorem imagePolynomial_natDegree [IsDomain R] {n : ℕ} (T : ParamTower R n)
    (g : MvPolynomial (Fin n) R) : (imagePolynomial T g).natDegree = T.degreeProduct := by
  let F := FractionRing R
  let K := AlgebraicClosure F
  let φ := (algebraMap F K).comp (algebraMap R F)
  exact ((imagePolynomial_monic T g).natDegree_map φ).symm.trans (imagePolynomial_degree T g φ)

end
end ZInQBlueprint.SunResultant.ParamTower
#print axioms ZInQBlueprint.SunResultant.ParamTower.satisfies_baseChange
#print axioms ZInQBlueprint.SunResultant.ParamTower.imagePolynomial_isRoot_iff
#print axioms ZInQBlueprint.SunResultant.ParamTower.rootTuples_baseChange
#print axioms ZInQBlueprint.SunResultant.ParamTower.imagePolynomial_eval_product
#print axioms ZInQBlueprint.SunResultant.ParamTower.imagePolynomial_map
#print axioms ZInQBlueprint.SunResultant.ParamTower.imagePolynomial_degree
#print axioms ZInQBlueprint.SunResultant.ParamTower.imagePolynomial_monic
#print axioms ZInQBlueprint.SunResultant.ParamTower.imagePolynomial_natDegree
