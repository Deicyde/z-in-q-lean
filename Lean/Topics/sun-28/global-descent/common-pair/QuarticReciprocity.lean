import SignedSections

/-! Interchanging the two coefficients on the two signed genus-one quartics. -/
namespace Sun28.CommonPair
open Sun28.PairedClasses
noncomputable section

/-- An affine point before projective or sign normalization. -/
def OnQuartic (k b d : ℚ) (P : ℚ×ℚ) : Prop :=
  P.2^2=k*d*(P.1^2-b)*(P.1^2+3*b)

def posSwap (b d : ℚ) (P : ℚ×ℚ) : ℚ×ℚ :=
  (P.2/(P.1^2-b),4*b*d*P.1/(P.1^2-b))

def negSwap (b d : ℚ) (P : ℚ×ℚ) : ℚ×ℚ :=
  (P.2/(P.1^2+3*b),12*b*d*P.1/(P.1^2+3*b))

theorem pos_chart {b d x y:ℚ} (h : OnQuartic 1 b d (x,y)) (den : x^2-b≠0) :
    let Q:=posSwap b d (x,y)
    Q.1^2-d=4*b*d/(x^2-b) ∧ Q.1^2+3*d=4*d*x^2/(x^2-b) := by
  change y^2=1*d*(x^2-b)*(x^2+3*b) at h
  dsimp [posSwap];constructor <;> field_simp [den] <;> linear_combination h

theorem neg_chart {b d x y:ℚ} (h : OnQuartic (-3) b d (x,y)) (den : x^2+3*b≠0) :
    let Q:=negSwap b d (x,y)
    Q.1^2-d=(-4)*d*x^2/(x^2+3*b) ∧ Q.1^2+3*d=12*b*d/(x^2+3*b) := by
  change y^2=(-3)*d*(x^2-b)*(x^2+3*b) at h
  dsimp [negSwap];constructor <;> field_simp [den] <;> linear_combination h

theorem pos_involution {b d : ℚ} (bn:b≠0) (dn:d≠0) {P : ℚ×ℚ}
    (h : OnQuartic 1 b d P) (den : P.1^2-b≠0) :
    OnQuartic 1 d b (posSwap b d P) ∧ posSwap d b (posSwap b d P)=P := by
  rcases P with ⟨x,y⟩
  obtain ⟨first,second⟩:=pos_chart h den
  constructor
  · unfold OnQuartic
    rw [first,second]
    dsimp [posSwap]
    ring
  · apply Prod.ext
    · change _ /( (posSwap b d (x,y)).1^2-d)=x
      rw [first]
      dsimp [posSwap]
      field_simp
    · change 4*d*b*_ /( (posSwap b d (x,y)).1^2-d)=y
      rw [first]
      dsimp [posSwap]
      field_simp

theorem neg_involution {b d : ℚ} (bn:b≠0) (dn:d≠0) {P : ℚ×ℚ}
    (h : OnQuartic (-3) b d P) (den : P.1^2+3*b≠0) :
    OnQuartic (-3) d b (negSwap b d P) ∧ negSwap d b (negSwap b d P)=P := by
  rcases P with ⟨x,y⟩
  have canonical : x^2+b*3≠0 := by simpa only [Prod.fst, mul_comm 3 b] using (show x^2+3*b≠0 from den)
  obtain ⟨first,second⟩:=neg_chart h den
  constructor
  · unfold OnQuartic
    rw [first,second]
    dsimp [negSwap]
    ring
  · apply Prod.ext
    · change _ /( (negSwap b d (x,y)).1^2+3*d)=x
      rw [second]
      dsimp [negSwap]
      field_simp [canonical]
    · change 12*d*b*_ /( (negSwap b d (x,y)).1^2+3*d)=y
      rw [second]
      dsimp [negSwap]
      field_simp [canonical]

end
end Sun28.CommonPair
#print axioms Sun28.CommonPair.pos_chart
#print axioms Sun28.CommonPair.neg_chart
#print axioms Sun28.CommonPair.pos_involution
#print axioms Sun28.CommonPair.neg_involution
