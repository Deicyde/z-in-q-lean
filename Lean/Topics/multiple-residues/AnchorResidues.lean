import ActualLocalResidues
import ActualAnchorBase23
import AnchorOrders23

namespace Prime23.Actual
open PhysicalProjection.Comparison (Q2 times norm sq)
open EllipticOrbit.Field (K D P Point ofPair coeffs ofPair_mul ofPair_coeffs coeffs_ofPair)
open ReciprocalDivision (reciprocal)

theorem reciprocal_fromCoordinates (S : Point) :
    reciprocal (D:=D) S=ActualBase.fromCoordinates S := by
  cases S <;> simp [reciprocal,EllipticOrbit.Law.abscissa,ActualBase.fromCoordinates,
    EllipticOrbit.Field.coordinates]

theorem base_one : orbit P 1=Base.qP := by
  simp only [orbit,one_zsmul,reciprocal_fromCoordinates,ActualBase.actual_qP,coeffs_ofPair]

theorem double_one : orbit ((2:ℕ) • P) 1=Base.qDouble := by
  simp only [orbit,one_zsmul,reciprocal_fromCoordinates,ActualBase.actual_qDouble,coeffs_ofPair]

theorem orbit_double (n : ℤ) : orbit ((2:ℕ) • P) n=orbit P (2*n) := by
  have h : (2:ℕ) • P=(2:ℤ) • P := rfl
  simp only [orbit,h,← mul_zsmul,mul_comm n 2]

/-- For each signed index both actual reciprocal abscissas are a square integer
multiple of their base times a principal unit. -/
theorem actual_normalized (n : ℤ) (hn : n≠0) :
    Normalized 2 Base.qP (orbit P n) (n:ℚ) ∧
    Normalized 3 Base.qDouble (orbit P (2*n)) (n:ℚ) := by
  constructor
  · exact dyadic_guarded (orbit_guarded (by decide) P) base_one n hn
  · rw [←orbit_double]
    exact triadic_guarded (orbit_guarded (by decide) _) double_one n hn

private theorem unscale {p : ℕ} [NeZero p] {v y : Q2} {c : ℚ} {r : Residues p}
    (hc : c≠0) (h : y=scale c v) (hv : PairRed p v r) :
    PairRed p (scale c⁻¹ y) r := by
  rw [h,show scale c⁻¹ (scale c v)=v by
    apply Prod.ext <;> simp [scale,hc]]
  exact hv

/-- Coefficientwise residues in Z_(p)[ρ], including the nilpotent class of ρ mod 2. -/
theorem actual_residues (n : ℤ) (hn : n≠0) :
    PairRed 2 (scale (8*(n:ℚ)^2)⁻¹ (orbit P n)) (1,0) ∧
    PairRed 3 (scale (9*(n:ℚ)^2)⁻¹ (orbit P (2*n))) (0,1) := by
  obtain ⟨⟨a,ar,ae⟩,⟨b,br,be⟩⟩:=actual_normalized n hn
  have two : Base.qP=scale 8 (scale (1/8) Base.qP) := by decide +kernel
  have three : Base.qDouble=scale 9 (scale (1/9) Base.qDouble) := by decide +kernel
  obtain ⟨u,ur,ue⟩:=normalized_output two Base.dyadic.1 ae ar
  obtain ⟨v,vr,ve⟩:=normalized_output three Base.triadic.2.1 be br
  rw [mul_comm ((n:ℚ)^2) (8:ℚ)] at ue
  rw [mul_comm ((n:ℚ)^2) (9:ℚ)] at ve
  have c : (n:ℚ)≠0 := by exact_mod_cast hn
  exact ⟨unscale (by positivity) ue ur,unscale (by positivity) ve vr⟩

private theorem field_scale (s : ℚ) (v : Q2) :
    ofPair (scale s v)=(algebraMap ℚ K s)*ofPair v := by
  change ofPair (scale s v) = (⟨s,0⟩:K) * ofPair v
  ext <;> simp [ofPair,scale]

private theorem field_ratio {p : ℕ} [NeZero p] {q y : Q2} {n : ℤ}
    (h : Normalized p q y (n:ℚ)) (hn : n≠0) (hq : ofPair q≠0) :
    PairRed p (coeffs (ofPair y / ((n:K)^2*ofPair q))) (1,0) := by
  obtain ⟨u,ur,eq⟩:=h
  have c : (n:K)≠0 := by exact_mod_cast hn
  have base : (n:K)^2*ofPair q≠0 := mul_ne_zero (pow_ne_zero 2 c) hq
  have e : ofPair y=((n:K)^2*ofPair q)*ofPair u := by
    rw [eq,ofPair_mul,field_scale,map_pow,map_intCast]
  rw [e,mul_comm _ (ofPair u),mul_div_cancel_right₀ _ base,coeffs_ofPair]
  exact ur

/-- The literal quotient by n² times the base reciprocal reduces to 1 at both primes. -/
theorem actual_quotient_residues (n : ℤ) (hn : n≠0) :
    PairRed 2 (coeffs (reciprocal (D:=D) (n • P) / ((n:K)^2*reciprocal (D:=D) P))) (1,0) ∧
    PairRed 3 (coeffs (reciprocal (D:=D) ((2*n) • P) /
      ((n:K)^2*reciprocal (D:=D) ((2:ℕ) • P)))) (1,0) := by
  obtain ⟨a,b⟩ := actual_normalized n hn
  have h := field_ratio a hn (by decide +kernel)
  have j := field_ratio b hn (by decide +kernel)
  have p1 : reciprocal (D:=D) P=ofPair Base.qP :=
    (reciprocal_fromCoordinates P).trans ActualBase.actual_qP
  have p2 : reciprocal (D:=D) ((2:ℕ) • P)=ofPair Base.qDouble :=
    (reciprocal_fromCoordinates _).trans ActualBase.actual_qDouble
  rw [p1,p2]
  exact ⟨h,j⟩

#print axioms actual_normalized
#print axioms actual_residues
#print axioms actual_quotient_residues
end Prime23.Actual
