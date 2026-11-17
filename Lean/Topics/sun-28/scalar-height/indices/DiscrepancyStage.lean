import CertificateHeights

/-! The Lucas discrepancy only involves the three indices s,t,z. -/
namespace Sun28.IndexHeights
open Sun28.Ordinary Sun28.FixedPreparation
noncomputable section

def tripleSize (n : Fin 4 → ℤ) : ℝ :=
  max 1 (max |(n 1 : ℝ)| (max |(n 2 : ℝ)| |(n 3 : ℝ)|))

def envelope (s t z : ℝ) := (|s|+2)*(|t|+|z|+1)

theorem lucas_envelope (s t z : ℝ) : |lucas s t z| < (envelope s t z)^2 := by
  let a:=|s|+2
  have a1 : 1≤a := by dsimp [a]; linarith [abs_nonneg s]
  have a2 : |s-2|≤a := by simpa [a,sub_eq_add_neg] using abs_add_le s (-2)
  have s1 : |s|≤a := by dsimp [a]; linarith
  have tp : 0≤|t|:=abs_nonneg _
  have zp : 0≤|z|:=abs_nonneg _
  have ap : 0≤a:=zero_le_one.trans a1
  have first : |t|^2 ≤ a^2*|t|^2 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ a1)
  have middle : |s| *|s-2| *|t| *|z|≤a^2*|t| *|z| := by
    apply mul_le_mul_of_nonneg_right _ zp
    apply mul_le_mul_of_nonneg_right _ tp
    simpa only [pow_two] using mul_le_mul s1 a2 (abs_nonneg _) ap
  have last :=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) a2 2) (sq_nonneg |z|)
  have tri : |lucas s t z|≤|t|^2+|s| *|s-2| *|t| *|z|+|s-2|^2*|z|^2+1 := by
    calc
      _ ≤ |t^2-s*(s-2)*t*z+(s-2)^2*z^2|+|-1| := by unfold lucas; exact abs_add_le _ _
      _ ≤ (|t^2-s*(s-2)*t*z|+|(s-2)^2*z^2|)+|-1| := by gcongr; exact abs_add_le _ _
      _ ≤ (|t^2|+|-(s*(s-2)*t*z)|+|(s-2)^2*z^2|)+|-1| := by gcongr; exact abs_add_le _ _
      _ = _ := by simp only [abs_neg,abs_mul,abs_pow,abs_one]
  change _ < (a*(|t|+|z|+1))^2
  have aa : 1<a^2 := by dsimp [a]; nlinarith [abs_nonneg s,sq_nonneg |s|]
  nlinarith only [tri,first,middle,last,aa,mul_nonneg (mul_nonneg (sq_nonneg a) tp) zp,
    mul_nonneg (sq_nonneg a) tp,mul_nonneg (sq_nonneg a) zp]

/-- An anisotropic critical-degree test, or the fixed-constant small radical test. -/
def LucasTest (n : Fin 4 → ℤ) (U : ℕ) : Prop :=
  (tripleSize n)^2 ≤ ordinary*(1+(U:ℝ)^24) ∨
  envelope (n 1) (n 2) (n 3) ≤ (U:ℝ)^32

theorem discrepancy_zero (n : Fin 4 → ℤ) (q : ℤ) (qn : q≠0)
    (anchorStep : n 1-1=(fixedMultiplier:ℤ)*q) {U : ℕ}
    (divides : (U:ℤ)^64 ∣ lucas (n 1) (n 2) (n 3))
    (bound : LucasTest n U) : lucas (n 1) (n 2) (n 3)=0 := by
  let Δ:=lucas (n 1) (n 2) (n 3)
  let B:=tripleSize n
  have S := fixed_multiplier_spec
  have rg:=scalar_step_range S.2.1 n q qn anchorStep
  have bs : |(n 1:ℝ)|≤B := by simp [B,tripleSize]
  have bt : |(n 2:ℝ)|≤B := by simp [B,tripleSize]
  have bz : |(n 3:ℝ)|≤B := by simp [B,tripleSize]
  have hM : (fixedMultiplier:ℝ)-1≤B := by
    have h: (fixedMultiplier:ℝ)≤ scalarStep n:=by exact_mod_cast rg.1
    linarith only [rg.2.2.2,h,bs]
  have big : 2≤B := by
    have r:(8:ℝ)≤fixedMultiplier:=by exact_mod_cast S.2.1
    linarith
  have cd : (Δ:ℝ)=lucas (n 1:ℝ) (n 2:ℝ) (n 3:ℝ) := by dsimp [Δ,lucas]; push_cast; ring
  by_contra nz
  have nd : 0<Δ.natAbs:=Int.natAbs_pos.mpr nz
  have k := Nat.le_of_dvd nd (Int.natAbs_dvd_natAbs.mpr divides)
  have base : (U:ℝ)^64≤|(Δ:ℝ)| := by
    rw [←Int.cast_abs,←Nat.cast_natAbs]
    simpa using (show ((U^64:ℕ):ℝ)≤((Δ.natAbs:ℕ):ℝ) by exact_mod_cast (show U^64≤Δ.natAbs by simpa using k))
  rcases bound with small|large
  · apply S.2.2.1 B hM
    have comp := lucas_abs_bound big bs bt bz
    rw [←cd] at comp
    have high : (U:ℝ)^64≤10*B^4 := by nlinarith only [base,comp,sq_nonneg (B^2)]
    have p:=Real.rpow_le_rpow (by positivity : 0≤(U:ℝ)^64) high (by norm_num : (0:ℝ)≤3/8)
    rw [←Real.rpow_natCast (U:ℝ) 64,←Real.rpow_mul (Nat.cast_nonneg _)] at p
    norm_num at p
    have op : 0≤ordinary := by unfold ordinary glazerConstant24; positivity
    exact small.trans (mul_le_mul_of_nonneg_left (add_le_add_right p _) op)
  · have E := lucas_envelope (n 1:ℝ) (n 2:ℝ) (n 3:ℝ)
    rw [←cd] at E
    have p:=pow_le_pow_left₀ (by unfold envelope; positivity : 0≤envelope (n 1) (n 2) (n 3)) large 2
    rw [←pow_mul] at p
    exact (not_lt_of_ge base) (E.trans_le p)

end
end Sun28.IndexHeights
#print axioms Sun28.IndexHeights.lucas_envelope
#print axioms Sun28.IndexHeights.discrepancy_zero
