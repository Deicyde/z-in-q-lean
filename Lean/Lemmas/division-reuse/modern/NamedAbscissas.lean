module

public import NamedResidues

@[expose] public section

namespace MarkedNamed
open EllipticOrbit.Field
open Prime23 (PairRed scale inverse inverse_clears Red)
open PhysicalProjection.Comparison (norm)

/-- The ordinary abscissa, evaluated using the named Weierstrass polynomials. -/
noncomputable def abscissaValue (n : ℤ) : K :=
  (E.Φ n).eval (ofPair (57/8,-7/2)) / (E.ΨSq n).eval (ofPair (57/8,-7/2))

private theorem inv_value (n : ℤ) : (value n)⁻¹ = abscissaValue n := by
  simp [value, abscissaValue, inv_div]

/-- Every nonzero signed multiple is finite, with the displayed ordinary abscissa. -/
theorem abscissa_coordinates (n : ℤ) (hn : n ≠ 0) :
    ∃ y : K, coordinates (n • P) = some (abscissaValue n,y) := by
  obtain ⟨hd, hf⟩ := evaluations_ne_zero n hn
  cases he : n • P with
  | zero =>
    have e := physical_named n
    rw [he] at e
    change (0 : K) = value n at e
    exact False.elim (div_ne_zero hd hf e.symm)
  | some x y h =>
    have e : x⁻¹ = value n := by
      have hmul := physical_named n
      rw [he] at hmul
      exact hmul
    have xval : x = abscissaValue n := by rw [← inv_value, ← e, inv_inv]
    exact ⟨y, congrArg (fun u => some (u,y)) xval⟩

theorem multiple_ne_zero (n : ℤ) (hn : n ≠ 0) : n • P ≠ 0 := by
  obtain ⟨y,hy⟩ := abscissa_coordinates n hn
  intro hz
  rw [hz] at hy
  cases hy

private theorem inverse_coeffs (w : K) (hn : norm (coeffs w) ≠ 0) :
    coeffs w⁻¹ = inverse (coeffs w) := by
  have prod : w * ofPair (inverse (coeffs w)) = 1 := by
    rw [← ofPair_coeffs w, ← ofPair_mul, coeffs_ofPair, inverse_clears hn]; rfl
  have nz : w ≠ 0 := by intro h; simp [h] at prod
  have eq : ofPair (inverse (coeffs w)) = w⁻¹ := by
    apply mul_left_cancel₀ nz
    rw [prod, mul_inv_cancel₀ nz]
  rw [← eq, coeffs_ofPair]

private theorem dyadic_inv {w : K} (h : PairRed 2 (coeffs w) (1,0)) :
    PairRed 2 (coeffs w⁻¹) (1,0) := by
  obtain ⟨hn, hr⟩ := h.invOne (by decide)
  rw [inverse_coeffs w hn]; exact hr

private theorem triadic_inv {w : K} (h : PairRed 3 (coeffs w) (0,1)) :
    PairRed 3 (coeffs w⁻¹) (0,2) := by
  have nr : Red 3 (norm (coeffs w)) 1 := h.norm
  obtain ⟨hn, u⟩ := nr.invOne (by decide)
  rw [inverse_coeffs w hn]
  exact ⟨h.1.mul u, h.2.neg.mul u⟩

private theorem scaled_coeffs (s : ℚ) (w : K) :
    scale s (coeffs w) = coeffs (algebraMap ℚ K s * w) := by
  change _ = coeffs ((⟨s,0⟩ : K) * w)
  apply Prod.ext <;> simp [scale,coeffs]

private theorem inverse_scaled (s : ℚ) (j : ℤ) :
    (algebraMap ℚ K s⁻¹ * value j)⁻¹ = algebraMap ℚ K s * abscissaValue j := by
  simp [mul_comm, inv_value]

/-- Clearing the poles of the ordinary abscissa gives residues 1 and 2√2. -/
theorem abscissa_residues (n : ℤ) (hn : n ≠ 0) :
    PairRed 2 (coeffs (8 * (n:K)^2 * abscissaValue n)) (1,0) ∧
    PairRed 3 (coeffs (9 * (n:K)^2 * abscissaValue (2*n))) (0,2) := by
  obtain ⟨h₂,h₃⟩ := named_residues n hn
  rw [scaled_coeffs] at h₂ h₃
  have d := dyadic_inv h₂
  have t := triadic_inv h₃
  rw [inverse_scaled] at d t
  simpa only [map_mul, map_ofNat, map_pow, map_intCast] using And.intro d t

#print axioms abscissa_coordinates
#print axioms multiple_ne_zero
#print axioms abscissa_residues
end MarkedNamed
