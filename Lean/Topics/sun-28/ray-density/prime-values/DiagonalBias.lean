import SplitObstruction

namespace Sun28.PrimeValues
open Finset Sun28.MixedSieve Sun28.PrimeLower
open scoped Classical
noncomputable section

/-- At normalized abelian norm -1, the two signed collision loci on a
single split norm circle coincide. There are exactly two points. -/
theorem split_diagonal {p : ℕ} [Fact p.Prime] (split : p%4=1) :
    (bad p (-1) true ∩ bad p (-1) false).card=2 := by
  have odd : p≠2 := by omega
  have two : (2:ZMod p)≠0 := by
    rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
    exact fun h=>odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h)
  have diff : (-1:ZMod p)≠1 := fun e=>two (by linear_combination -e)
  have sub : bad p (-1) true ⊆ bad p (-1) false := by
    intro z hit
    have a:=z.property
    have b:=(mem_filter.mp hit).2
    change z.val.1^2+z.val.2^2= -1 at a
    change (z.val.1+1)^2+z.val.2^2=0 at b
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change (z.val.1+ -1)^2+z.val.2^2=0
    linear_combination 2*a-b
  rw [Finset.inter_eq_left.mpr sub,split_bad_card split,ite_eq_right diff]

theorem split_diagonal_rate {p : ℕ} [Fact p.Prime] (split : p%4=1) :
    (((bad p (-1) true ∩ bad p (-1) false).card : ℝ)/Fintype.card (Circle p (-1))) =
      2/((p:ℝ)-1) := by
  have odd : p≠2 := by omega
  have n := circle_card (p:=p) (t:=-1) odd (by simp)
  rw [legendreSym.at_neg_one odd,ZMod.χ₄_nat_eq_if_mod_four] at n
  have modn : p%2≠0 := by omega
  simp [split,modn] at n
  have n' : (Fintype.card (Circle p (-1)) : ℝ)=(p:ℝ)-1 := by exact_mod_cast n
  rw [split_diagonal split,n']
  norm_num

theorem exceeds_square_rate {p : ℕ} [Fact p.Prime] (split : p%4=1) (large : 703≤p) :
    1404/((p:ℝ)-1)^2 <
      (((bad p (-1) true ∩ bad p (-1) false).card : ℝ)/Fintype.card (Circle p (-1))) := by
  rw [split_diagonal_rate split]
  have pp : (703:ℝ) ≤ p := by exact_mod_cast large
  have better : (703:ℝ)<p := by exact_mod_cast (show 703<p by omega)
  have pos : 0<(p:ℝ)-1 := by linarith
  field_simp
  nlinarith

end
end Sun28.PrimeValues
#print axioms Sun28.PrimeValues.split_diagonal
#print axioms Sun28.PrimeValues.split_diagonal_rate
#print axioms Sun28.PrimeValues.exceeds_square_rate
