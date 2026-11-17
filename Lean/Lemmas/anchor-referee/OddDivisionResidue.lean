import Std

namespace AnchorCollision.Residue
open Lean.Grind
variable {F : Type} [Field F]

private theorem live {a b : F} (az : a≠0) (bz : b≠0) : a*b^3≠0 := by
  rw [show a*b^3=a*b*b*b by grobner]
  have mul {x y : F} (hx : x≠0) (hy : y≠0) : x*y≠0 :=
    fun eq=>(Field.of_mul_eq_zero eq).elim hx hy
  exact mul (mul (mul az bz) bz) bz

/-- The odd division polynomials all survive at a smooth nonidentity point of order two. -/
theorem odd_nonzero (ψ : Nat→F) (one : ψ 1≠0) (three : ψ 3≠0)
    (even : ∀j,ψ (2*j)=0)
    (step : ∀k,2≤k→ψ (2*k+1)=ψ (k+2)*(ψ k)^3-ψ (k-1)*(ψ (k+1))^3) :
    ∀ k,ψ (2*k+1)≠0 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases small : k<2
    · rcases (show k=0 ∨ k=1 by omega) with rfl | rfl
      · exact one
      · exact three
    have h:=step k (by omega)
    let j:=k/2
    have parity : k=2*j ∨ k=2*j+1 := by dsimp [j];omega
    rcases parity with ek|ok
    · have e0 : ψ (k+2)=0 := (show k+2=2*(j+1) by omega) ▸ even (j+1)
      have o0 : ψ (k-1)≠0 := (show k-1=2*(j-1)+1 by omega) ▸ ih (j-1) (by omega)
      have o1 : ψ (k+1)≠0 := (show k+1=2*j+1 by omega) ▸ ih j (by omega)
      have nz:=live o0 o1
      rw [h,e0,Semiring.zero_mul]
      exact fun z=>nz (by grobner)
    · have o0 : ψ (k+2)≠0 := (show k+2=2*(j+1)+1 by omega) ▸ ih (j+1) (by omega)
      have o1 : ψ k≠0 := ok ▸ ih j (by omega)
      have e0 : ψ (k-1)=0 := (show k-1=2*j by omega) ▸ even j
      have nz:=live o0 o1
      rw [h,e0,Semiring.zero_mul]
      exact fun z=>nz (by grobner)

/-- On the short Weierstrass cubic, the first nontrivial odd polynomial at a root. -/
theorem psi_three_at_root (A B e : F) (root : e^3+A*e+B=0) :
    3*e^4+6*A*e^2+12*B*e-A^2= -(3*e^2+A)^2 := by
  have eq : B= -e^3-A*e := by grobner
  rw [eq];grobner

/-- The reduced abscissa is the same smooth two-torsion abscissa for every odd label. -/
theorem odd_abscissa (e : F) (ψ : Nat→F) (one : ψ 1≠0) (three : ψ 3≠0)
    (even : ∀j,ψ (2*j)=0)
    (step : ∀k,2≤k→ψ (2*k+1)=ψ (k+2)*(ψ k)^3-ψ (k-1)*(ψ (k+1))^3) (k : Nat) :
    (e*(ψ (2*k+1))^2-ψ (2*k+2)*ψ (2*k))/(ψ (2*k+1))^2=e := by
  have nz:=odd_nonzero ψ one three even step k
  have sq : (ψ (2*k+1))^2≠0 := by
    rw [show (ψ (2*k+1))^2=ψ (2*k+1)*ψ (2*k+1) by grobner]
    exact fun h=>(Field.of_mul_eq_zero h).elim nz nz
  rw [even k,Semiring.mul_zero,show e*(ψ (2*k+1))^2-0=e*(ψ (2*k+1))^2 by grobner]
  have mul : ((e*(ψ (2*k+1))^2)/(ψ (2*k+1))^2)*(ψ (2*k+1))^2=e*(ψ (2*k+1))^2 :=
    Field.div_mul_cancel sq
  have diff : ((e*(ψ (2*k+1))^2)/(ψ (2*k+1))^2-e)*(ψ (2*k+1))^2=0 := by grobner
  have := (Field.of_mul_eq_zero diff).resolve_right sq
  grobner

end AnchorCollision.Residue
#print axioms AnchorCollision.Residue.odd_nonzero
#print axioms AnchorCollision.Residue.odd_abscissa
