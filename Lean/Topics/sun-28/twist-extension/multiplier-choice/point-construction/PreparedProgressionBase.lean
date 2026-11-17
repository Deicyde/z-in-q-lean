import SquareFamilySpecialization
import FiniteScalarPole

namespace Sun28.PointConstruction
open Sun28.Ordinary Sun28.ScalarHeight Sun28.TwistRank Sun28.FixedPreparation Sun28.FinitePole
  Sun28.ContactFactors Sun28.PreparedPoles
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 700000

def scalarCoefficient : ℕ := 7895415

def progressionDen (n : ℤ) : ℤ := 1+(7895415*(gamma:ℤ))*(n+2)
def progression (n : ℤ) : ℚ := (gamma:ℚ)/(progressionDen n:ℚ)

theorem denominator_facts (n:ℕ) :
    2*(scalarCoefficient:ℤ)*gamma < progressionDen n ∧
    (scalarCoefficient*gamma).Coprime (progressionDen n).natAbs := by
  let L : ℕ := scalarCoefficient*gamma
  have eq : progressionDen n = ((L*(n+2)+1:ℕ):ℤ) := by
    dsimp [L,progressionDen,scalarCoefficient]; ring
  have comp : L.Coprime (L*(n+2)+1) := by simp
  refine ⟨?_,by simpa only [eq,Int.natAbs_natCast] using comp⟩
  rw [eq];push_cast
  have castL : (L:ℤ)=(scalarCoefficient:ℤ)*(gamma:ℤ) := by simp [L]
  nlinarith only [castL,Int.natCast_nonneg n,mul_nonneg (Int.natCast_nonneg L) (Int.natCast_nonneg n)]

/-- Uniform coprime fraction calculation. All coefficient sizes are arbitrary. -/
private theorem basic_interval (c g : ℕ) (D:ℤ) (cp:0<c) (gp:0<g)
    (big:2*(c:ℤ)*g < D) (cop:(c*g).Coprime D.natAbs) :
    let B:ℚ := (c:ℚ)*((g:ℚ)/(D:ℚ))^2
    IsSquare B.den ∧ 0 < B ∧ B < 1/2 := by
  dsimp only
  have cr : (1:ℚ) ≤ c := by exact_mod_cast cp
  have gr : (0:ℚ) < g := by exact_mod_cast gp
  have cp' : (0:ℚ) < c := by exact_mod_cast cp
  have big' : 2*(c:ℚ)*g<(D:ℚ) := by exact_mod_cast big
  have dr : (0:ℚ)<D := lt_trans (mul_pos (mul_pos (by norm_num) cp') gr) big'
  have pos : 0<(c:ℚ)*((g:ℚ)/(D:ℚ))^2 := by positivity
  have less : (c:ℚ)*((g:ℚ)/(D:ℚ))^2 < 1/2 := by
    rw [div_pow]
    have sj := pow_lt_pow_left₀ big' (mul_pos (mul_pos (by norm_num) cp') gr).le (by decide : 2≠0)
    have aux : 2*(c:ℚ)*(g:ℚ)^2 ≤ (2*(c:ℚ)*g)^2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr cr) (mul_nonneg cp'.le (sq_nonneg (g:ℚ)))]
    field_simp [dr.ne']; nlinarith only [sj,aux]
  refine ⟨?_,pos,less⟩
  have cd : c.Coprime D.natAbs := Nat.Coprime.of_dvd_left (dvd_mul_right c g) cop
  have gd : g.Coprime D.natAbs := Nat.Coprime.of_dvd_left (dvd_mul_left g c) cop
  have denpos : 0<D^2 := pow_pos (by exact_mod_cast dr) 2
  have cden : ((c:ℤ)*(g:ℤ)^2).natAbs.Coprime (D^2).natAbs := by
    simpa only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] using (cd.mul_left (gd.pow_left 2)).pow_right 2
  have de := Rat.den_div_eq_of_coprime denpos cden
  have eqn : (((c:ℤ)*(g:ℤ)^2:ℤ):ℚ)/((D^2:ℤ):ℚ)=(c:ℚ)*((g:ℚ)/(D:ℚ))^2 := by push_cast;ring
  rw [eqn] at de
  use D.natAbs
  have h := congrArg Int.natAbs de
  simpa only [Int.natAbs_natCast,pow_two,Int.natAbs_mul] using h

theorem interval_den (n:ℕ) : IsSquare (inputB (progression n)).den ∧ 0 < inputB (progression n) ∧ inputB (progression n) < 1/2 := by
  obtain ⟨big,cop⟩:=denominator_facts n
  exact basic_interval scalarCoefficient gamma (progressionDen n) (by decide) gamma_positive big cop

end
end Sun28.PointConstruction
#print axioms Sun28.PointConstruction.denominator_facts
#print axioms Sun28.PointConstruction.interval_den
