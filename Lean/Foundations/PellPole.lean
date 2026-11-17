import QuarticPole

namespace PellPole

/-- A conic point supplies four witnesses on the literal elliptic block. -/
theorem conic_block (B U w : Rat) (hw : B*(w^2-1)=3*U^2) :
    QuarticPole.LiteralAt B U := by
  refine ⟨1, 0, 4*B*U, B*w, ?_, ?_⟩
  · grobner
  · dsimp
    have h₁ : (B*w)^2-B*(1*(B-U^2))=4*B*U^2 := by grobner
    have h₂ : (B*w)^2+3*(B*(1*(B-U^2)))=4*B^2 := by grobner
    rw [h₁,h₂]
    grobner

theorem conic_poles (b w : Rat) (hw : 17*(w^2-1)=3*b) :
    QuarticPole.ZeroPole b ∧ QuarticPole.ScalarPole b := by
  have h := conic_block (17*b) b w (by grobner)
  exact ⟨h, 0, b, by unfold QuarticPole.Preparation; grobner, h⟩

#print axioms conic_block
#print axioms conic_poles
end PellPole
