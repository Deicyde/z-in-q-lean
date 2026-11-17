import MarkedConductor
import OrdinateHeight

/-! An integral model for the j-invariant associated to a supported Mordell point. -/
namespace Sun28.HeightCubics.Refinement
open Sun28.FiveMarkUnits ZInQBlueprint.TwistDescent Height
noncomputable section

def cleared (x y:ℚ) : WeierstrassCurve ℤ :=
  ⟨0,0,0,-3*x.num*(x.den:ℤ)^3*(y.den:ℤ)^4,
    2*y.num*(x.den:ℤ)^6*(y.den:ℤ)^5⟩

theorem cleared_invariants (x y:ℚ) {a:ℤ} (eq:y^2=x^3+(a:ℚ)) :
    (cleared x y).Δ = -1728*a*((x.den:ℤ)*y.den)^12 ∧
    (((cleared x y).c₄:ℤ):ℚ)=144*x*((x.den:ℚ)*y.den)^4 := by
  have xd:(x.den:ℚ)≠0:=by exact_mod_cast x.den_nz
  have yd:(y.den:ℚ)≠0:=by exact_mod_cast y.den_nz
  have xx:(x.num:ℚ)=x*(x.den:ℚ):=by
    rw [←Rat.num_div_den x];simp
  have yy:(y.num:ℚ)=y*(y.den:ℚ):=by
    rw [←Rat.num_div_den y];simp
  constructor
  · apply Int.cast_injective (α:=ℚ)
    simp only [cleared,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,WeierstrassCurve.b₈]
    push_cast
    rw [xx,yy]
    linear_combination -1728*((x.den:ℚ)*y.den)^12*eq
  · simp only [cleared,WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄]
    push_cast;rw [xx];ring

theorem cleared_j (x y:ℚ) {a:ℤ} (an:a≠0) (eq:y^2=x^3+(a:ℚ)) :
    (cleared x y).Δ≠0 ∧ jRatio (cleared x y) = -1728*x^3/(a:ℚ) := by
  obtain ⟨disc,c4⟩:=cleared_invariants x y eq
  have xd:(x.den:ℤ)≠0:=by exact_mod_cast x.den_nz
  have yd:(y.den:ℤ)≠0:=by exact_mod_cast y.den_nz
  constructor
  · rw [disc]
    exact mul_ne_zero (mul_ne_zero (by decide) an) (pow_ne_zero _ (mul_ne_zero xd yd))
  · unfold jRatio;rw [c4,disc];push_cast
    field_simp [show (x.den:ℚ)≠0 by exact_mod_cast x.den_nz,
      show (y.den:ℚ)≠0 by exact_mod_cast y.den_nz,show (a:ℚ)≠0 by exact_mod_cast an]
    ring

theorem supported_conductor {S:Finset ℕ} {x y:ℚ} {a:ℤ} (an:a≠0)
    (supp:a.natAbs.primeFactors⊆S) (ix:IsSInteger S x) (iy:IsSInteger S y)
    (eq:y^2=x^3+(a:ℚ)) (data:EllipticEstimates (cleared x y)) :
    data.N∣62208*(primeProduct S)^2 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
  intro p k prime small
  apply (pow_dvd_pow p ((prime.pow_dvd_iff_le_factorization data.pos.ne').1 small)).trans
  by_cases p2:p=2
  · subst p;exact (pow_dvd_pow 2 data.two).trans ((show 2^8∣62208 by decide).trans (dvd_mul_right _ _))
  by_cases p3:p=3
  · subst p;exact (pow_dvd_pow 3 data.three).trans ((show 3^5∣62208 by decide).trans (dvd_mul_right _ _))
  by_cases mem:p∈S
  · exact (pow_dvd_pow p (data.tame p prime p2 p3)).trans
      ((pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun n:ℕ=>n) mem) 2).trans (dvd_mul_left _ _))
  have good:¬(p:ℤ)∣(cleared x y).Δ:=by
    rw [(cleared_invariants x y eq).1]
    intro z
    have pri:Prime (p:ℤ):=by simpa [Int.prime_iff_natAbs_prime] using prime
    rcases pri.dvd_mul.mp z with sw|den
    · rcases pri.dvd_mul.mp sw with c|c
      · have dvd:p∣1728:=by simpa using Int.natAbs_dvd_natAbs.mpr c
        have h6: p∣6:=prime.dvd_of_dvd_pow (dvd.trans (show 1728∣6^6 by decide))
        rcases prime.dvd_mul.mp (show p∣2*3 from h6) with h|h
        · exact p2 ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp h)
        · exact p3 ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_three).mp h)
      · exact mem (supp (Nat.mem_primeFactors.mpr
          ⟨prime,by simpa using Int.natAbs_dvd_natAbs.mpr c,Int.natAbs_ne_zero.mpr an⟩))
    · rcases pri.dvd_mul.mp (pri.dvd_of_dvd_pow den) with h|h
      · exact mem (ix (Nat.mem_primeFactors.mpr ⟨prime,Int.natCast_dvd_natCast.mp h,x.den_nz⟩))
      · exact mem (iy (Nat.mem_primeFactors.mpr ⟨prime,Int.natCast_dvd_natCast.mp h,y.den_nz⟩))
  rw [data.good p prime good,pow_zero]
  exact one_dvd _

end
end Sun28.HeightCubics.Refinement
#print axioms Sun28.HeightCubics.Refinement.cleared_invariants
#print axioms Sun28.HeightCubics.Refinement.cleared_j
#print axioms Sun28.HeightCubics.Refinement.supported_conductor
