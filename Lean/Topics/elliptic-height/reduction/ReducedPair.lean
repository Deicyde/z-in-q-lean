import EuclideanDivision

namespace EllipticHeight.Reduction
open QuadraticInt

private theorem reverse_bezout {b t : R} (pr : coprime b t) (q : R) :
    coprime (plus (mul b q) t) b := by
  obtain ⟨u,v,h⟩:=pr
  refine ⟨v,minus u (mul q v),?_⟩
  calc
    _ = plus (mul b u) (mul t v) := by
      apply Prod.ext <;> dsimp [plus,mul,minus] <;> grobner
    _ = _ := h

private theorem factor_step (g b q t : R) :
    plus (mul (mul g b) q) (mul g t)=mul g (plus (mul b q) t) := by
  apply Prod.ext <;> dsimp [plus,mul] <;> grobner

/-- Every pair factors through a common divisor and a pair with an integral
Bézout identity, including (0,0). -/
theorem reduce_pair (x y : R) :
    ∃ g a b : R, x=mul g a ∧ y=mul g b ∧ coprime a b := by
  generalize size : (norm y).natAbs=m
  induction m using Nat.strongRecOn generalizing x y with
  | ind m ih =>
    by_cases zero : y=(0,0)
    · subst y
      refine ⟨x,(1,0),(0,0),?_,?_,(1,0),(0,0),by decide⟩
      · apply Prod.ext <;> simp [mul]
      · apply Prod.ext <;> simp [mul]
    · let r:=remainder x y
      let q:=quotient x y
      have small : (norm r).natAbs<m := size ▸ strict_descent x y zero
      obtain ⟨g,b,t,hy,hr,pr⟩:=ih (norm r).natAbs small y r rfl
      refine ⟨g,plus (mul b q) t,b,?_,hy,reverse_bezout pr q⟩
      calc
        x = plus (mul y q) r := division_identity x y
        _ = plus (mul (mul g b) q) (mul g t) := by rw [hy,hr]
        _ = _ := factor_step ..

#print axioms reduce_pair
end EllipticHeight.Reduction
