import PrimeFibre
import FlagApplication

namespace Sun28.PrimeLower

open Sun28.MixedSieve Sun28.NormSieve Sun28.WeightedSelection
open Sun28.ContactFactors Sun28.QuadricSieve Sun28.MediumSieve
open ManuscriptV15.Arithmetic
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Inert off-diagonal obstructions force a single rational residue pair. -/
theorem inert_collision {u w : ZMod p} {c : ι → ZMod p}
    (inert : p % 4 = 3) (hc : Function.Injective c)
    (z : (i : ι) → Circle p (norms c u w i)) (hit : z ∈ obstructed _) :
    u = 1 ∧ w = 0 := by
  obtain ⟨i,j,hi,hj⟩ := (obstructed_iff z).mp hit
  have left {a b : ZMod p} (eq : a^2+b^2=0) : a=0 ∧ b=0 := by
    have e : a^2 = -b^2 := eq_neg_of_add_eq_zero_left eq
    have bz : b=0 := by
      by_contra ne
      exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' ne e inert
    exact ⟨by simpa [bz] using e,bz⟩
  have ai : ((z i).val.1+1)^2+(z i).val.2^2=0 := (Finset.mem_filter.mp hi).2
  have aj : ((z j).val.1-1)^2+(z j).val.2^2=0 := by
    simpa [sub_eq_add_neg] using (Finset.mem_filter.mp hj).2
  obtain ⟨hx,hy⟩ := left ai
  obtain ⟨ha,hb⟩ := left aj
  have nx : (z i).val.1 = -1 := by linear_combination hx
  have ny : (z j).val.1 = 1 := by linear_combination ha
  have ni := (z i).property
  have nj := (z j).property
  rw [nx,hy] at ni
  rw [ny,hb] at nj
  have vi : norms c u w i = 1 := by simpa using ni.symm
  have vj : norms c u w j = 1 := by simpa using nj.symm
  have two : (2 : ZMod p) ≠ 0 := by
    rw [←Nat.cast_ofNat, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => (show p≠2 by omega) ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h)
  have diff : i ≠ j := by
    rintro rfl
    apply two
    linear_combination nx-ny
  have we : (c i-c j)*w^2=0 := by
    unfold norms at vi vj
    linear_combination vi-vj
  have wz := (pow_eq_zero_iff (by decide : 2≠0)).mp
    ((mul_eq_zero.mp we).resolve_left (sub_ne_zero.mpr (hc.ne diff)))
  refine ⟨?_,wz⟩
  simpa [norms,wz] using vi

/-- Outside the fixed coefficient exceptions, a rational congruence enforces the actual
local order condition for every pair of oriented generators. -/
theorem inert_atPrime {A : Fin 3 → ℚ} {d κ : ℕ} {T : Finset ℕ} {H Y : ℝ}
    (a : Candidate A d H Y) (pos : 0<d) (large : exceptionalBound A d < p)
    (inert : p%4=3) (outside : p∉T) (aux : p∉κ.primeFactors)
    (avoid : ¬((a.u : ZMod p)=1 ∧ (a.v : ZMod p)=0)) : atPrime a.gaussian T κ p := by
  apply (atPrime_iff_fibre a T κ p (by omega) outside aux).mpr
  apply fun hit => avoid (inert_collision inert ?_ _ hit)
  intro i j eq
  by_contra ne
  apply Sun28.ConeFibres.reduced_gap_ne_zero pos large ne
  simpa [Sun28.SieveTail.gap, coefficients,Int.cast_sub] using sub_eq_zero.mpr eq

end Sun28.PrimeLower
#print axioms Sun28.PrimeLower.inert_collision
#print axioms Sun28.PrimeLower.inert_atPrime
