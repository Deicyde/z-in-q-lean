import JacobianTwists

namespace ZInQBlueprint.Diagonal210
open WeierstrassCurve
noncomputable section

/-- In an algebraic squareclass group taking all four triple products twice
returns each class. The integral identity remembers the discarded square. -/
theorem double_triple {K : Type*} [CommSemiring K] (v : Fin 4 → K) (i : Fin 4) :
    triple (triple v) i = v i * (v 0*v 1*v 2*v 3)^2 := by
  fin_cases i <;> norm_num [triple] <;> ring

def comparisonRoot : Fin 4 → ℚ := ![315/4,1029/8,21/8,21]
theorem coefficient_scales (i : Fin 4) :
    triple coefficient i = scale i*(comparisonRoot i)^2 ∧ comparisonRoot i ≠ 0 ∧ coefficient i ≠ 0 := by
  fin_cases i <;> norm_num [triple,coefficient,scale,comparisonRoot]

private theorem triple_mul_sq (v w : Fin 4 → ℚ) (i : Fin 4) :
    triple (fun j=>v j*(w j)^2) i = triple v i*(triple w i)^2 := by
  fin_cases i <;> simp [triple] <;> ring

/-- The four rational Jacobians determine all four coefficients of the cover,
as rational squareclasses. Equality of four j-invariants alone is weaker. -/
theorem recover_coefficients (c : Fin 4 → ℚ) (C : Fin 4 → VariableChange ℚ)
    (hn : ∀ i,c i≠0) (E : ∀ i,C i • model i (triple c i)=publishedJacobian i) :
    ∃ v : Fin 4 → ℚ, ∀ i, v i≠0 ∧ c i=coefficient i*(v i)^2 := by
  classical
  choose u hu using fun i=>class_from_jacobian (C i) (E i)
  let w (i : Fin 4) := u i / comparisonRoot i
  have wn (i : Fin 4) : w i≠0 := div_ne_zero (hu i).1 (coefficient_scales i).2.1
  have prodw (i : Fin 4) : triple w i≠0 := by
    fin_cases i <;> simp [triple,wn]
  have eqs : triple c = fun i=>triple coefficient i*(w i)^2 := by
    ext i
    rw [(hu i).2,(coefficient_scales i).1]
    dsimp [w]
    field_simp [(coefficient_scales i).2.1]
  let U := c 0*c 1*c 2*c 3
  let V := coefficient 0*coefficient 1*coefficient 2*coefficient 3
  have un : U≠0 := by dsimp [U];exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2)) (hn 3)
  have vn : V≠0 := by norm_num [V,coefficient]
  refine ⟨fun i=>V*triple w i/U,fun i=>⟨div_ne_zero (mul_ne_zero vn (prodw i)) un,?_⟩⟩
  have h : c i * U^2 = coefficient i*V^2*(triple w i)^2 := calc
    c i*U^2 = triple (triple c) i := (double_triple c i).symm
    _ = triple (fun j=>triple coefficient j*(w j)^2) i := congrArg (fun q=>triple q i) eqs
    _ = _ := by rw [triple_mul_sq,double_triple]
  field_simp [un]
  linear_combination h

/-- Affine equation of the full degree-sixteen sign cover at a rational slope. -/
def radicand (s : ℚ) (i : Fin 4) := coefficient i*(s-mark i)
def Fibre (K : Type*) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚ) (s : ℚ) :=
  {y : Fin 4 → K // ∀ i,(y i)^2=algebraMap ℚ K (c i*(s-mark i))}

/-- Actual rational coordinate rescalings give an isomorphism on the fibres
over every extension field. This includes the finite branch values. -/
def fibreEquiv {K : Type*} [Field K] [Algebra ℚ K] {c : Fin 4 → ℚ}
    (v : Fin 4 → ℚ) (h : ∀ i,v i≠0 ∧ c i=coefficient i*(v i)^2) (s : ℚ) :
    Fibre K c s ≃ Fibre K coefficient s where
  toFun y := ⟨fun i=>y.1 i/algebraMap ℚ K (v i),by
    intro i
    have ne := (map_ne_zero (algebraMap ℚ K)).mpr (h i).1
    rw [div_pow,y.2 i,(h i).2]
    simp only [map_mul,map_pow]
    field_simp [ne]⟩
  invFun y := ⟨fun i=>y.1 i*algebraMap ℚ K (v i),by
    intro i
    rw [mul_pow,y.2 i,(h i).2]
    simp only [map_mul,map_pow]
    ring⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    exact div_mul_cancel₀ _ ((map_ne_zero (algebraMap ℚ K)).mpr (h i).1)
  right_inv y := by
    apply Subtype.ext
    funext i
    exact mul_div_cancel_right₀ _ ((map_ne_zero (algebraMap ℚ K)).mpr (h i).1)

theorem fibre_of_jacobians (K : Type*) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚ)
    (C : Fin 4 → VariableChange ℚ) (hn : ∀ i,c i≠0)
    (E : ∀ i,C i • model i (triple c i)=publishedJacobian i) (s : ℚ) :
    Nonempty (Fibre K c s ≃ Fibre K coefficient s) := by
  obtain ⟨v,h⟩ := recover_coefficients c C hn E
  exact ⟨fibreEquiv v h s⟩

end
end ZInQBlueprint.Diagonal210
#print axioms ZInQBlueprint.Diagonal210.double_triple
#print axioms ZInQBlueprint.Diagonal210.coefficient_scales
#print axioms ZInQBlueprint.Diagonal210.recover_coefficients
#print axioms ZInQBlueprint.Diagonal210.fibre_of_jacobians
