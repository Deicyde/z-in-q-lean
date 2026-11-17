import CoarseConic
import Mathlib.RingTheory.Invariant.Basic

/-! Pointwise-labelled real multiplication on a rational model. -/
namespace ZInQBlueprint.RealMultiplication
open ZInQBlueprint.CoarseConic ZInQBlueprint.SixContact

theorem real_coordinate (u : ℚ) :
    (-(27*J u+16))/J u = (4*h u/r u)^2 := by
  have hk : -(27*J u+16) = -(4*h u)^2 := by linear_combination second_square u
  rw [hk,first_square,div_pow,neg_div_neg_eq]

variable {G O E : Type*} [Group G] [Ring O] [Ring E] [MulSemiringAction G E]
variable (ι : O →+* E)

/-- A polarized intertwiner commutes with the image of the order when it
belongs to {±1}. Cancellation then gives pointwise descent. -/
theorem fixed_embedding
    (intertwines : ∀ g : G, ∃ a : Eˣ, (∀ r, (g • ι r)*a=a*ι r) ∧
      ∀ r, Commute (a:E) (ι r)) (g : G) (r : O) : g • ι r = ι r := by
  obtain ⟨a,ha,hc⟩ := intertwines g
  exact a.isUnit.mul_left_inj.mp ((ha r).trans (hc r).eq)

def descendedEmbedding (intertwines : ∀ g : G, ∃ a : Eˣ, (∀ r, (g • ι r)*a=a*ι r) ∧
    ∀ r, Commute (a:E) (ι r)) : O →+* FixedPoints.subring E G :=
  ι.codRestrict _ (fun r g => fixed_embedding ι intertwines g r)

theorem descendedEmbedding_injective
    (hι : Function.Injective ι) (intertwines : ∀ g : G, ∃ a : Eˣ,
    (∀ r, (g • ι r)*a=a*ι r) ∧ ∀ r, Commute (a:E) (ι r)) :
    Function.Injective (descendedEmbedding ι intertwines) :=
  fun _ _ h => hι (congrArg Subtype.val h)

end ZInQBlueprint.RealMultiplication
#print axioms ZInQBlueprint.RealMultiplication.real_coordinate
#print axioms ZInQBlueprint.RealMultiplication.fixed_embedding
#print axioms ZInQBlueprint.RealMultiplication.descendedEmbedding_injective
