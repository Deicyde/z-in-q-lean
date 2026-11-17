import BinaryQuartic435
import ConductorProjection28

namespace Sun28.LocalQuartics
/- The underlying set of ZMod (n+1) is Fin (n+1), but the ring structures
come from different hierarchies. Transport their natural-number operations. -/
set_option maxHeartbeats 600000 in
theorem residue_point {p : ℕ} [hp : Fact p.Prime] (odd : p≠2) (a b c d k : ZMod p)
    (det : a*d-b*c≠0) (unit : k≠0) :
    ∃ u y : ZMod p,y^2=k*(a*u^2+b)*(c*u^2+d) := by
  rcases p with _|n
  · exact (Nat.not_prime_zero hp.out).elim
  have pr : BinaryQuartic.Prime (n+1) := ⟨hp.out.two_le,fun d hd=>
    (Nat.dvd_prime hp.out).mp hd⟩
  have eo : (n+1)%2=1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two odd)
  let A : Fin (n+1) := a
  let B : Fin (n+1) := b
  let C : Fin (n+1) := c
  let D : Fin (n+1) := d
  let K : Fin (n+1) := k
  have de : A*D-B*C≠0 := det
  have ku : K≠0 := unit
  obtain ⟨u,y,E⟩ := BinaryQuartic.finite_affine pr eo A B C D K de ku
  refine ⟨u,y,?_⟩
  have clean : y^2=K*((A*u^2+B)*(C*u^2+D)) := by
    simpa only [BinaryQuartic.form,one_pow,mul_one] using E
  let uf : ZMod (n+1) := u
  let yf : ZMod (n+1) := y
  have eq : yf^2=k*((a*uf^2+b)*(c*uf^2+d)) := clean
  exact eq.trans (mul_assoc _ _ _).symm

end Sun28.LocalQuartics
#print axioms Sun28.LocalQuartics.residue_point
