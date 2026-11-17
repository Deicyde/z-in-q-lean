import CoverField

namespace ZInQBlueprint.Diagonal210
open IntermediateField

/-- The smooth projective model is the intersection of these three diagonal
quadrics, in the coordinates (w,y₀,y₁,y₂,y₃). -/
def quadrics {K : Type*} [Field K] (w : K) (y : Fin 4 → K) : Prop :=
  7*(y 1)^2-3*(y 0)^2=21*w^2 ∧ (y 2)^2+3*(y 0)^2= -50421*w^2 ∧
    16*(y 3)^2-96*(y 0)^2= -7203*w^2

theorem affine_quadrics {K : Type*} [Field K] [CharZero K] (y : Fin 4 → K) :
    quadrics 1 y ↔ ∃ s : K, ∀ i, (y i)^2=(coefficient i:K)*(s-(mark i:K)) := by
  constructor
  · rintro ⟨e1,e2,e3⟩
    refine ⟨-(y 0)^2/7,?_⟩
    intro i
    fin_cases i <;> norm_num [coefficient,mark] at *
    · ring
    · linear_combination e1/7
    · linear_combination e2
    · linear_combination e3/16
  · rintro ⟨s,h⟩
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    norm_num [coefficient,mark] at h0 h1 h2 h3
    unfold quadrics
    constructor <;> try constructor <;> norm_num
    · linear_combination 7*h1-3*h0
    · linear_combination h2+3*h0
    · linear_combination 16*h3-96*h0

theorem no_real_point {w : ℝ} {y : Fin 4 → ℝ} (h : quadrics w y) : w=0 ∧ ∀ i,y i=0 := by
  obtain ⟨e1,e2,e3⟩ := h
  have w0 : w=0 := by nlinarith [sq_nonneg (y 2),sq_nonneg (y 0),sq_nonneg w]
  rw [w0] at e1 e2 e3
  have a : y 0=0 := by nlinarith [sq_nonneg (y 2),sq_nonneg (y 0)]
  refine ⟨w0,?_⟩
  intro i
  rw [a] at e1 e2 e3
  fin_cases i <;> norm_num at *
  · exact a
  · nlinarith [sq_nonneg (y 1)]
  · nlinarith [sq_nonneg (y 2)]
  · nlinarith [sq_nonneg (y 3)]

end ZInQBlueprint.Diagonal210
#print axioms ZInQBlueprint.Diagonal210.affine_quadrics
#print axioms ZInQBlueprint.Diagonal210.no_real_point
