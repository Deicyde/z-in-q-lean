import QuadraticContact
import ScalarBudget

/-! The four integral rows of the scalar octic permit arbitrary rational centres. -/
namespace Sun28.PointPencils
open Height Sun28.ScalarHeight Sun28.ScalarLucas
noncomputable section
set_option maxRecDepth 8192

def xCoeff : Fin 4 → ℤ := ![2,1,1,64]
def yCoeff : Fin 4 → ℤ := ![3,1,-1199,439]
def scalarRow (i : Fin 4) (a b : ℤ) : ℤ := form (xCoeff i) (yCoeff i) a b

theorem scalar_rows (x : ℚ) : (∏ i : Fin 4, (scalarRow i x.num x.den:ℚ)) =
    Sun28.WitnessHeight.octic x*(x.den:ℚ)^8 := by
  have num : (x.num:ℚ)=x*(x.den:ℚ) :=
    (div_eq_iff (by exact_mod_cast x.den_nz)).mp x.num_div_den
  rw [Fin.prod_univ_four]
  change (((2*x.num^2+3*(x.den:ℤ)^2:ℤ):ℚ) * ((1*x.num^2+1*(x.den:ℤ)^2:ℤ):ℚ) *
    ((1*x.num^2+(-1199)*(x.den:ℤ)^2:ℤ):ℚ) * ((64*x.num^2+439*(x.den:ℤ)^2:ℤ):ℚ)) = _
  push_cast
  rw [num]
  unfold WitnessHeight.octic
  ring

def scaledCap (i : Fin 4) (u v : ℤ) (x : ℚ) : ℝ :=
  let l:=xCoeff i
  let m:=yCoeff i
  let B:=max |u| |v| *(|l*m| +max |l| |m|)*(det u v x.num x.den)^2
  (B:ℝ)/(|scalarRow i u v|:ℤ)

theorem height_from_row (x : ℚ) (i : Fin 4) {u v : ℤ} (nonzero : scalarRow i u v≠0)
    (away : det u v x.num x.den≠0) (square : IsSquare (scalarRow i u v*scalarRow i x.num x.den)) :
    logHeight₁ (beta x)≤2*Real.log (scaledCap i u v x)+4 := by
  have live : ∀ j : Fin 4, xCoeff j≠0 ∧ yCoeff j≠0 := by decide
  have h:=coordinates_of_square (live i).1 (live i).2 away square
  let N:=max x.num.natAbs x.den
  have ne : 0<(N:ℝ) := by dsimp [N];exact_mod_cast x.den_pos.trans_le (le_max_right ..)
  have zn : 0 < |scalarRow i u v| := abs_pos.mpr nonzero
  have cap : (N:ℝ)≤ scaledCap i u v x := by
    change (N:ℝ)≤_/((|scalarRow i u v|:ℤ):ℝ)
    apply (le_div_iff₀ (by exact_mod_cast zn)).mpr
    have map : (N:ℤ)=max |x.num| |(x.den:ℤ)| := by simp [N,Nat.cast_max]
    rw [show (N:ℝ) = ((N:ℤ):ℝ) by norm_cast]
    exact_mod_cast map ▸ h
  have hgt:=ScalarPencil.beta_height x
  rw [Rat.logHeight₁_eq_log_max x] at hgt
  change logHeight₁ (beta x)≤2*Real.log (N:ℝ)+4 at hgt
  linarith only [hgt,Real.log_le_log ne cap]

def RowTest (x : ℚ) : Prop :=
  ∃ (i : Fin 4) (u v : ℤ), scalarRow i u v≠0 ∧ det u v x.num x.den≠0 ∧
    IsSquare (scalarRow i u v*scalarRow i x.num x.den) ∧
    2*Real.log (scaledCap i u v x)+4≤ scalarAllowance x

theorem of_row_test (x : ℚ) (test : RowTest x) :
    logHeight₁ (beta x)≤ scalarAllowance x := by
  obtain ⟨i,u,v,nonzero,away,square,cap⟩:=test
  exact (height_from_row x i nonzero away square).trans cap

end
end Sun28.PointPencils
#print axioms Sun28.PointPencils.scalar_rows
#print axioms Sun28.PointPencils.height_from_row
#print axioms Sun28.PointPencils.of_row_test
