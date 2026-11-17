import QuadricsProj
/-! The standard affine pieces of the projective scheme, identified with the square-root charts. -/
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace ZInQBlueprint.SexticEmbedding
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
local notation "Pol" => MvPolynomial (Fin 4) K
abbrev ChartRing (c : Fin 7 → K) (j : Fin 5) := MvPolynomial (Fin 4) K ⧸
    (equationsIdeal c).toIdeal.map (TauCeti.dehomogenize j)

def chartVariable (c : Fin 7 → K) (j : Fin 5) : Fin 4 → ChartRing c j :=
    Ideal.Quotient.mk _ ∘ X

/-- Evaluation on the dehomogenized quotient exists if the four equations hold in the test ring. -/
def evaluateChart (c : Fin 7 → K) (j : Fin 5) (a : Fin 4 → S)
    (h : ∀ i, generators (algebraMap K S ∘ c) (j.insertNth 1 a) i = 0) :
    ChartRing c j →ₐ[K] S :=
  Ideal.Quotient.liftₐ _ (aeval a) fun p hp => by
    have e : (equationsIdeal c).toIdeal.map (TauCeti.dehomogenize j) ≤ RingHom.ker (aeval a) := by
      apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change aeval a (TauCeti.dehomogenize j (quadrics c i)) = 0
      rw [TauCeti.aeval_dehomogenize,eval_quadrics]
      exact h i
    exact e hp

@[simp] theorem evaluateChart_variable (c : Fin 7 → K) (j : Fin 5) (a : Fin 4 → S) (h) (i : Fin 4) :
    evaluateChart c j a h (chartVariable c j i) = a i :=
  (Ideal.Quotient.liftₐ_apply _ _ _ _).trans (aeval_X a i)

/-- The universal four-tuple satisfies the original four equations after the omitted coordinate is set to one. -/
theorem chartRelations (c : Fin 7 → K) (j : Fin 5) : ∀ i,
    generators (algebraMap K (ChartRing c j) ∘ c) (j.insertNth 1 (chartVariable c j)) i = 0 := by
  intro i
  rw [← eval_quadrics, ← TauCeti.aeval_dehomogenize]
  have hmap : (aeval (chartVariable c j)) = Ideal.Quotient.mkₐ K
       ((equationsIdeal c).toIdeal.map (TauCeti.dehomogenize j)) :=
    by
      apply MvPolynomial.algHom_ext
      intro k
      exact aeval_X _ k
  rw [hmap]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _
    (show quadrics c i ∈ (equationsIdeal c).toIdeal from Ideal.subset_span (Set.mem_range_self i)))

theorem chart_ext (c : Fin 7 → K) (j : Fin 5) {f g : ChartRing c j →ₐ[K] S}
    (h : ∀ i, f (chartVariable c j i) = g (chartVariable c j i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

open BinaryCover Polynomial
/-- Insert the missing coordinate in the finite or reciprocal chart. -/
def pivot (b : Bool) : Fin 5 := if b then 0 else 3
def coefficients (c : Fin 7 → K) (b : Bool) : Fin 7 → K := if b then c ∘ Fin.rev else c
def affineTuple (b : Bool) (x y : S) : Fin 4 → S :=
  if b then ![x,x^2,x^3,y] else ![x^3,x^2,x,y]
def xIndex (b : Bool) : Fin 4 := if b then 0 else 2

theorem affineTuple_equations (c : Fin 7 → K) (b : Bool) (x y : S)
    (h : y^2 = sextic (algebraMap K S ∘ coefficients c b) x) :
    ∀ i, generators (algebraMap K S ∘ c) ((pivot b).insertNth 1 (affineTuple b x y)) i = 0 := by
  apply (generators_vanish _ _).mpr
  cases b
  · change equations _ (x^3) (x^2) x 1 y
    exact (finite_chart ..).mpr ⟨rfl,rfl,h⟩
  · change equations _ 1 x (x^2) (x^3) y
    exact (infinity_chart ..).mpr ⟨rfl,rfl,h⟩

theorem chart_xy (c : Fin 7 → K) (b : Bool) :
    let v := chartVariable c (pivot b)
    (v 3)^2 = sextic (algebraMap K (ChartRing c (pivot b)) ∘ coefficients c b) (v (xIndex b)) ∧
    v = affineTuple b (v (xIndex b)) (v 3) := by
  have e := (generators_vanish _ _).mp (chartRelations c (pivot b))
  cases b
  · let v := chartVariable c 3
    change equations _ (v 0) (v 1) (v 2) 1 (v 3) at e
    obtain ⟨h₀,h₁,h⟩ := (finite_chart ..).mp e
    refine ⟨h,?_⟩
    funext i
    fin_cases i
    · exact h₀
    · exact h₁
    · rfl
    · rfl
  · let v := chartVariable c 0
    change equations _ 1 (v 0) (v 1) (v 2) (v 3) at e
    obtain ⟨h₁,h₂,h⟩ := (infinity_chart ..).mp e
    refine ⟨h,?_⟩
    funext i
    fin_cases i
    · rfl
    · exact h₁
    · exact h₂
    · rfl

private theorem sextic_eval (c : Fin 7 → K) (x : S) :
    Polynomial.aeval x (equationPolynomial c) = sextic (algebraMap K S ∘ c) x := by
  simp [equationPolynomial,sextic]

abbrev SquareChart (c : Fin 7 → K) (b : Bool) := Cover (equationPolynomial (coefficients c b))
def squareX (c : Fin 7 → K) (b : Bool) : SquareChart c b :=
  algebraMap K[X] _ Polynomial.X
def squareY (c : Fin 7 → K) (b : Bool) : SquareChart c b := QuadraticAlgebra.omega
private theorem squareEq (c : Fin 7 → K) (b : Bool) :
    squareY c b ^2 = sextic (algebraMap K (SquareChart c b) ∘ coefficients c b) (squareX c b) := by
  have h := ordinate_square (AlgHom.id K (SquareChart c b))
  exact h.trans (sextic_eval _ _)

def chartToSquare (c : Fin 7 → K) (b : Bool) : ChartRing c (pivot b) →ₐ[K] SquareChart c b :=
  evaluateChart c (pivot b) (affineTuple b (squareX c b) (squareY c b))
    (affineTuple_equations c b _ _ (squareEq c b))
def squareToChart (c : Fin 7 → K) (b : Bool) : SquareChart c b →ₐ[K] ChartRing c (pivot b) :=
  let v := chartVariable c (pivot b)
  affinePoint _ (v (xIndex b)) (v 3) ((chart_xy c b).1.trans (sextic_eval _ _).symm)

theorem squareToChart_X (c : Fin 7 → K) (b : Bool) :
    squareToChart c b (squareX c b) = chartVariable c (pivot b) (xIndex b) := by
  let x := chartVariable c (pivot b) (xIndex b)
  let y := chartVariable c (pivot b) 3
  change Polynomial.aeval x (Polynomial.X : K[X]) + Polynomial.aeval x (0:K[X])*y = x
  simp

theorem squareToChart_Y (c : Fin 7 → K) (b : Bool) :
    squareToChart c b (squareY c b) = chartVariable c (pivot b) 3 := by
  let x := chartVariable c (pivot b) (xIndex b)
  let y := chartVariable c (pivot b) 3
  change Polynomial.aeval x (0:K[X]) + Polynomial.aeval x (1:K[X])*y = y
  simp

/-- The dehomogenized ring is the original or reciprocal quadratic algebra. -/
def chartRingEquiv (c : Fin 7 → K) (b : Bool) : ChartRing c (pivot b) ≃ₐ[K] SquareChart c b :=
  AlgEquiv.ofAlgHom (chartToSquare c b) (squareToChart c b) (by
    apply AlgHom.ext
    intro z
    let F := (chartToSquare c b).comp (squareToChart c b)
    change F z = (AlgHom.id K _ : SquareChart c b →ₐ[K] _) z
    have x : F (squareX c b) = squareX c b := by
      change chartToSquare c b (squareToChart c b (squareX c b)) = _
      rw [squareToChart_X]
      unfold chartToSquare
      rw [evaluateChart_variable]
      cases b <;> rfl
    have y : F (squareY c b) = squareY c b := by
      change chartToSquare c b (squareToChart c b (squareY c b)) = _
      rw [squareToChart_Y]
      unfold chartToSquare
      rw [evaluateChart_variable]
      cases b <;> rfl
    exact (affinePoint_image F z).trans ((congrArg₂
      (fun a d => Polynomial.aeval a z.re + Polynomial.aeval a z.im * d) x y).trans
      (affinePoint_image (AlgHom.id K _) z).symm)) (by
    apply chart_ext
    intro i
    change squareToChart c b (chartToSquare c b (chartVariable c (pivot b) i)) = _
    unfold chartToSquare
    rw [evaluateChart_variable]
    rw [congrFun (chart_xy c b).2 i]
    cases b <;> fin_cases i <;> simp [affineTuple,map_pow,squareToChart_X,squareToChart_Y])

/-- On each of the two actual Proj opens the coordinate ring is the stated square-root algebra. -/
def projectiveChartIso (c : Fin 7 → K) (b : Bool) :
    (coordinateOpen c (pivot b)).toScheme ≅ Spec (.of (SquareChart c b)) :=
  affineChartIso c (pivot b) ≪≫ Scheme.Spec.mapIso (chartRingEquiv c b).toRingEquiv.toCommRingCatIso.op.symm

end
end ZInQBlueprint.SexticEmbedding
#print axioms ZInQBlueprint.SexticEmbedding.chartRingEquiv
#print axioms ZInQBlueprint.SexticEmbedding.projectiveChartIso
