import OddRootBalls
import ZInQKernel.RouteK.Selmer.Good
import ZInQKernel.RouteK.Selmer.BadOdd

namespace Sun28.MarkedOdd
open Sun28.SelmerRealization ZInQ.RouteK.Selmer
variable {p : ℕ} [Fact p.Prime]

theorem bad_classes (p2 : p≠2) (p3 : p≠3) {l : ℕ} (pl : p ∣ l) (sl : Squarefree l)
    {a b : ℤ} (an : a≠0) (bn : b≠0) (h : Cover (Qp p) l a b) :
    TorsionValues (a:Qp p) (b:Qp p) (l:Qp p) := by
  have ln : (l:Qp p)≠0 := Nat.cast_ne_zero.mpr sl.ne_zero
  rcases chart_of_cover an bn h with h|⟨x,u,v,w,E,F,G⟩
  · exact Or.inl h
  rcases root_balls p2 p3 ln E F G with h|⟨nx,ny,nz,sq,_,_⟩
  · exact h
  exfalso
  have hpos := norm_pos_iff.mpr ln
  have nv : x*(x-(l:Qp p))*(x+3*(l:Qp p)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (norm_pos_iff.mp (nx.symm ▸ hpos)) (norm_pos_iff.mp (ny.symm ▸ hpos)))
      (norm_pos_iff.mp (nz.symm ▸ hpos))
  apply padic_norm_ne_zpow_odd nv sq (-2)
  rw [norm_mul,norm_mul,nx,ny,nz,padic_norm_natCast_of_squarefree pl sl]
  norm_num
  ring

theorem good_support (p2 : p≠2) (p3 : p≠3) {l : ℕ} (pl : ¬p ∣ l)
    {a b : ℤ} (sa : Squarefree a) (sb : Squarefree b) (h : Cover (Qp p) l a b) :
    ¬(p:ℤ) ∣ a ∧ ¬(p:ℤ) ∣ b := by
  have dl : ¬(p:ℤ)∣ (l:ℤ) := fun h => pl (by exact_mod_cast h)
  have ln : (l:Qp p)≠0 := by intro h;apply pl;rw [Nat.cast_eq_zero.mp h];exact dvd_zero _
  have N : ‖(l:Qp p)‖=1 := by simpa using padic_norm_intCast_eq_one (p:=p) dl
  have N3 : ‖(3:Qp p)‖=1 := by
    apply padic_norm_intCast_eq_one (c:=3)
    intro h
    exact p3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp (by exact_mod_cast h))
  have filter (z : ℤ) (hz : Squarefree z) (s : Qp p) (unit : ‖s‖=1) (H : SqEq (z:Qp p) s) :
      ¬(p:ℤ)∣z := by
    have v := even_valuation_of_sqEq_unit unit H
    rw [Padic.valuation_intCast] at v
    exact not_dvd_of_squarefree_of_even_padicValInt hz ((Int.even_coe_nat _).mp v)
  have tors (H : TorsionValues (a:Qp p) (b:Qp p) (l:Qp p)) : ¬(p:ℤ)∣a ∧ ¬(p:ℤ)∣b := by
    rcases H with ⟨A,B⟩|⟨A,B⟩|⟨A,B⟩|⟨A,B⟩ <;>
      exact ⟨filter a sa _ (by simp [N,N3,norm_mul]) A,filter b sb _ (by simp [N]) B⟩
  rcases chart_of_cover sa.ne_zero sb.ne_zero h with H|⟨x,u,v,w,E,F,G⟩
  · exact tors (Or.inl H)
  rcases root_balls p2 p3 ln E F G with H|⟨_,ny,nz,_,A,B⟩
  · exact tors H
  · exact ⟨filter a sa _ (nz.trans N) A,filter b sb _ (ny.trans N) B⟩

theorem bad_basis (p2 : p≠2) (p3 : p≠3) {l : ℕ} (pl : p ∣ l) (sl : Squarefree l)
    {a b : ℤ} (an : a≠0) (bn : b≠0) (h : Cover (Qp p) l a b) :
    ∃ i j : ℕ, i<2 ∧ j<2 ∧ IsSquare (((a*(l:ℤ)^i*3^j:ℤ):Qp p)) ∧
      IsSquare (((b*(-(l:ℤ))^j:ℤ):Qp p)) := by
  rcases bad_classes p2 p3 pl sl an bn h with ⟨A,B⟩|⟨A,B⟩|⟨A,B⟩|⟨A,B⟩
  · exact ⟨0,0,by decide,by decide,by simpa using A.isSquare_mul,by simpa using B.isSquare_mul⟩
  · exact ⟨1,0,by decide,by decide,by simpa using A.isSquare_mul,by simpa using B.isSquare_mul⟩
  · exact ⟨0,1,by decide,by decide,by simpa using A.isSquare_mul,by simpa using B.isSquare_mul⟩
  · exact ⟨1,1,by decide,by decide,by simpa [mul_comm,mul_assoc,mul_left_comm] using A.isSquare_mul,
      by simpa using B.isSquare_mul⟩

end Sun28.MarkedOdd
#print axioms Sun28.MarkedOdd.good_support
#print axioms Sun28.MarkedOdd.bad_classes
#print axioms Sun28.MarkedOdd.bad_basis
