import BranchTransvectant

/-! Coefficients of the product of six linear factors, grouped into two cubics. -/
namespace ZInQBlueprint.BranchI4
open Polynomial SexticInvariants SexticThetaHeight
noncomputable section

/-- Convolve the coefficients of the first and last three linear factors. -/
def rootsCoeff (r : Fin 6 → ℂ) : ℕ → ℂ :=
  let a := -(r 0*r 1*r 2)
  let b := r 0*r 1+r 0*r 2+r 1*r 2
  let c := -(r 0+r 1+r 2)
  let d := -(r 3*r 4*r 5)
  let e := r 3*r 4+r 3*r 5+r 4*r 5
  let g := -(r 3+r 4+r 5)
  fun
    | 0 => a*d
    | 1 => b*d+a*e
    | 2 => c*d+b*e+a*g
    | 3 => d+c*e+b*g+a
    | 4 => e+c*g+b
    | 5 => g+c
    | 6 => 1
    | _ => 0

private def sixTerms (c : ℕ → ℂ) : ℂ[X] :=
  C (c 0)+C (c 1)*X+C (c 2)*X^2+C (c 3)*X^3+C (c 4)*X^4+C (c 5)*X^5+C (c 6)*X^6

theorem expand_roots (r : Fin 6 → ℂ) :
    (∏ i, (X-C (r i))) = sixTerms (rootsCoeff r) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (X-C (r 0))*((X-C (r 1))*((X-C (r 2))*((X-C (r 3))*((X-C (r 4))*(X-C (r 5)))))) = _
  simp only [sixTerms,rootsCoeff,map_add,map_mul,map_neg,map_one]
  ring

theorem factor_coeff (f : ℚ[X]) (hd : f.natDegree = 6) (r : Fin 6 → ℂ)
    (hr : Function.Injective r) (hh : ∀ i, aeval (r i) f = 0) (k : Fin 7) :
    (f.coeff k : ℂ) = f.leadingCoeff * rootsCoeff r k := by
  have h := congrArg (fun p : ℂ[X] => p.coeff k) (factorization f hd r hr hh)
  rw [expand_roots] at h
  simp only [coeff_map, coeff_C_mul] at h
  refine h.trans ?_
  congr 1
  fin_cases k <;> norm_num [sixTerms, coeff_C_mul, coeff_add, coeff_X_pow, coeff_X, coeff_C]

end
end ZInQBlueprint.BranchI4
#print axioms ZInQBlueprint.BranchI4.expand_roots
#print axioms ZInQBlueprint.BranchI4.factor_coeff
