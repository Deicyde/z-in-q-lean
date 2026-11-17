import DiamondIndex
import TameSign

namespace ZInQBlueprint.DiamondHeight
noncomputable section

/-- A quadratic times a Dirichlet character has image order at most twice
any exponent of the latter. For a normalized quaternionic isogeny this square
identity is the one obtained on the fourth exterior power of the Tate module. -/
theorem determinant_from_square {G:Type*} [Group G] (ε χ : G →* ℂˣ) {m:ℕ}
    (mp:0<m) (square:∀g,(ε g * χ g)^2=1) (ann:∀g,(χ g)^m=1) : ε.ker.index ≤ 2*m := by
  apply character_index ε (Nat.mul_pos (by decide) mp)
  intro g
  have h:=congrArg (fun z:ℂˣ=>z^m) (square g)
  change ((ε g*χ g)^2)^m=1^m at h
  rw [←pow_mul,mul_pow,one_pow] at h
  have c : (χ g)^(2*m)=1 := by rw [Nat.mul_comm,pow_mul,ann,one_pow]
  rwa [c,mul_one] at h

/-- On the scalar kernel field the determinant is quadratic. The order of the
square character on the full absolute Galois group can yield a smaller bound. -/
theorem determinant_at_sign_field {G:Type*} [Group G] (b:G → ℂˣ) (χ ε:G →* ℂˣ)
    (bs:∀g,(b g)^2=χ g) (eqn:∀g,(ε g*χ g)^2=1) {g:G} (trivial:b g=1) :
    (ε g)^2=1 := by
  have t : χ g=1 := by rw [←bs,trivial,one_pow]
  simpa only [t,mul_one] using eqn g

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.determinant_from_square
#print axioms ZInQBlueprint.DiamondHeight.determinant_at_sign_field
