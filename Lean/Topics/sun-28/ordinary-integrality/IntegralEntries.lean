import IntegralMultiples

namespace Sun28.OrdinaryIntegrality
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.Ordinary Sun28.ScalarTrace Sun28.FixedPreparation Sun28.Forward Sun28.WitnessIndices
noncomputable section
attribute [local irreducible] anchor paperGenerator
set_option maxHeartbeats 30000
set_option maxRecDepth 500
theorem anchor_formal {q : ℕ} [Fact q.Prime] (small : q≤23) {π : Zs}
    (pr : Prime π) (above : π∣(q:Zs)) :
    anchor • paperGenerator sqrt2_sq ∈ W1 (vP π pr) (-(3-sqrt2)^2) :=
  ((mem_formalFilt_iff (paper_integral pr) (if q=2 then 4 else 2) (anchor • paperGenerator sqrt2_sq)).mp
    (fixed_anchor_prepared (q:=q) (π:=π) small pr above)).1

private theorem anchor_inputs {q : ℕ} [Fact q.Prime] (small : q≤23) {π : Zs}
    (prime : Prime π) (above : π∣(q:Zs)) (j n : ℤ) (mul : anchor∣j) :
    let P:=paperGenerator sqrt2_sq
    Vge (vP π prime) 0 (reciprocal (b:= -(3-sqrt2)^2) ((j*n) • P)) ∧
    Vge (vP π prime) 0 (ordinaryRatio (b:= -(3-sqrt2)^2) P (j*n) j) := by
  have near : anchor • paperGenerator sqrt2_sq ∈ W1 (vP π prime) (-(3-sqrt2)^2) :=
    anchor_formal small prime above
  exact multiples_of_anchor small prime above (-(3-sqrt2)^2) (paper_integral prime)
    (paperGenerator sqrt2_sq) anchor j n near mul

theorem tests_prime {q : ℕ} [Fact q.Prime] (small : q≤23) {π : Zs} (prime : Prime π)
    (above : π∣(q:Zs)) (c h : ℤ) (n : Fin 4 → ℤ) (β : ℤ)
    (hc : anchor∣c) (hh : anchor∣h) (i : OrdinaryTest) :
    Vge (vP π prime) 0 (ordinaryTests sqrt2_sq conjugation c h n (fun j=>h*n j) (β:ℚ) i) := by
  let v:=vP π prime
  have primary (j : Fin 4) :=
    anchor_inputs (q:=q) (π:=π) small prime above h (n j) hh
  have primary0 := anchor_inputs (q:=q) (π:=π) small prime above h 1 hh
  have hd:=dvd_sub hh hc
  have second (j : Fin 4) :=
    anchor_inputs (q:=q) (π:=star π) small (prime_star prime) (star_dvd_natCast above) (h-c) (n j) hd
  have second0:=anchor_inputs (q:=q) (π:=star π) small (prime_star prime) (star_dvd_natCast above) (h-c) 1 hd
  have sigma (x : K0) (a : Vge (vP (star π) (prime_star prime)) 0 x) : Vge v 0 (conjugation x) := by
    change (0:WithTop ℤ)≤vP π prime (star x)
    rw [←vP_star prime];exact a
  have diff (j : Fin 4) : h*n j-c*n j=(h-c)*n j := by ring
  cases i with
  | h => simpa only [ordinaryTests,mul_one] using primary0.1
  | u j => exact (primary j).1
  | v₀ => simpa only [ordinaryTests,mul_one] using sigma _ second0.1
  | v j => simp only [ordinaryTests,diff];exact sigma _ (second j).1
  | difference j =>
    simp only [ordinaryTests,diff]
    exact (primary j).2.sub (sigma _ (second j).2)
  | delta => exact lucas_integral v (primary 1).2 (primary 2).2 (primary 3).2
  | beta =>
    simp only [ordinaryTests,map_intCast]
    exact (primary 0).2.sub (vge_intCast β)

theorem points_prime {q : ℕ} [Fact q.Prime] (small : q≤23) {π : Zs} (prime : Prime π)
    (above : π∣(q:Zs)) {w : NinePoints} {M c a} (rep : Consequences w M c a) (β : ℤ)
    (hc : anchor∣c) (hh : anchor∣a.h) (labels : ∀ j,a.m j=a.h*a.n j) (i : OrdinaryTest) :
    Vge (vP π prime) 0 (ordinaryAt w M c (β:ℚ) i) ∧
    Vge (vP π prime) 0 (conjugation (ordinaryAt w M c (β:ℚ) i)) := by
  rw [←ordinaryAt_eq rep,show a.m=(fun j=>a.h*a.n j) from funext labels]
  refine ⟨tests_prime small prime above c a.h a.n β hc hh i,?_⟩
  change (0:WithTop ℤ)≤vP π prime (star _)
  rw [←vP_star prime]
  exact tests_prime small (prime_star prime) (star_dvd_natCast above) c a.h a.n β hc hh i

end
#print axioms anchor_formal
#print axioms tests_prime
#print axioms points_prime
end Sun28.OrdinaryIntegrality
