import Std

namespace HeightSpecialization.WeakTrace
open Lean.Grind Std

/-- The common order-two Kummer character is equivalent to a trace.
    The index set may be the absolute Galois group, with keep specifying
    the subgroup fixing the quadratic extension. -/
theorem cocycle_trace {G I : Type} [IntModule G] (keep : I → Prop) [DecidablePred keep]
    (act : I → G → G) (mapAdd : ∀ i x y, act i (x+y) = act i x + act i y)
    (mapSub : ∀ i x y, act i (x-y) = act i x - act i y)
    (U : G) (c : I → G) (orderTwo : ∀ i, c i+c i=0)
    (liftU : ∀ i, act i U=U+c i) :
    (∃ V, ∀ i, act i V=(if keep i then V else -V)+c i) ↔
    (∃ R, ∀ i, act i R=if keep i then R else U+U-R) := by
  constructor
  · rintro ⟨V,hV⟩
    refine ⟨U+V, ?_⟩
    intro i
    rw [mapAdd,liftU,hV]
    have _ := orderTwo i
    by_cases h : keep i <;> simp only [h,if_true,if_false] <;> grind
  · rintro ⟨R,hR⟩
    refine ⟨R-U, ?_⟩
    intro i
    rw [mapSub,hR,liftU]
    have _ := orderTwo i
    by_cases h : keep i <;> simp only [h,if_true,if_false] <;> grind

/-- Coordinates of the moving weak companion after division by s+√b. -/
theorem quadric_identity {K : Type} [Field K] (s b X Y : K) :
    (s*X+b*Y)^2-b*(X+s*Y)^2=(s^2-b)*(X^2-b*Y^2) := by grobner

end HeightSpecialization.WeakTrace
#print axioms HeightSpecialization.WeakTrace.cocycle_trace
#print axioms HeightSpecialization.WeakTrace.quadric_identity
