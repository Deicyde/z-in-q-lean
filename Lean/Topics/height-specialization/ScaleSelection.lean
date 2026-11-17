import SelectedComparison
import ProductWires

namespace HeightSpecialization
open StructuralReduction StructuralReduction.Transfer84 IndependentIndices IndependentIndices.Assembly
open ProjectionFibres ProjectionFibres.Actual ProjectionFibres.HeightSupport ProjectionFibres.Comparison
open WitnessTransfer.Height
set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

def tallest (x : Fin 84→Rat) := maximumFrame (fun f=>H (slope x f))

theorem physical_scale_heights {x : Fin 84→Rat} (dom : domain x) :
    let U:=H (slope x (tallest x))
    H (atWire x 1249)≤U ∧ (H (atWire x 1252))^2≤U ∧
    (H (atWire x 1249)*H (atWire x 1252))^2≤U^3 := by
  have nz : cell x 13≠0 := by
    intro e
    apply noMark x .first dom
    rw [(slope_values x).1,e]
    simp [P]
  obtain ⟨a,b,c⟩:=slope_values x
  apply scale_heights nz
  · rw [←a];exact le_maximum (fun f=>H (slope x f)) .first
  · rw [←b];exact le_maximum (fun f=>H (slope x f)) .second
  · rw [←c];exact le_maximum (fun f=>H (slope x f)) .third

private theorem radical_pos (ps : List Nat) (h : ∀ p∈ps,0<p) : 0<radical ps := by
  induction ps with
  | nil => decide
  | cons p ps ih => exact Nat.lcm_pos (h p (by simp)) (ih (fun q hq=>h q (List.mem_cons_of_mem _ hq)))

theorem scale_radical_pos (x : Fin 84→Rat) (f : Scale) : 0<M x f :=
  radical_pos _ (fun p hp=>(Nat.lt_trans (by decide : 0<1) ((mem_fullPrimes _ _).mp hp).1.1))

def ProductHeight (x : Fin 84→Rat) (ns : Labels) :=
  2^(4*(labelSize ns)^2) ≤ 2^30*(H (atWire x 1249)*H (atWire x 1252))^3

def SlopeHeight (x : Fin 84→Rat) (f : Scale) :=
  (H (slope x f))^2 ≤ 2^(4+3*(detectorConstant*(M x f)^17))

private theorem combine_heights {N L U V : Nat} (h : 32≤V)
    (a : 2^(4*N^2)≤2^30*L^3) (b : L^2≤U^3) (c : U^2≤2^(4+3*V)) :
    N^2<2*V := by
  have power : 2^(16*N^2) ≤ 2^(156+27*V) := by
    calc
      _ = (2^(4*N^2))^4 := by rw [←Nat.pow_mul];congr 1;omega
      _ ≤ (2^30*L^3)^4 := Nat.pow_le_pow_left a 4
      _ = 2^120*(L^2)^6 := by simp only [Nat.mul_pow,←Nat.pow_mul]
      _ ≤ 2^120*(U^3)^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left b 6)
      _ = 2^120*(U^2)^9 := by rw [←Nat.pow_mul,←Nat.pow_mul]
      _ ≤ 2^120*(2^(4+3*V))^9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left c 9)
      _ = _ := by rw [←Nat.pow_mul,←Nat.pow_add];congr 1;omega
  have e:=(Nat.pow_le_pow_iff_right (by decide : 1<2)).mp power
  omega

theorem root_bound_at_tallest {x : Fin 84→Rat} {ns : Labels} (dom : domain x)
    (roots : ProductHeight x ns) (bound : SlopeHeight x (tallest x)) :
    (labelSize ns)^2 < rootConstant*(M x (tallest x))^17 := by
  have pos:=Nat.pow_pos (scale_radical_pos x (tallest x)) (n:=17)
  have margin : 32≤detectorConstant := by decide +kernel
  have big : 32≤detectorConstant*(M x (tallest x))^17 :=
    Nat.le_trans margin (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left detectorConstant pos)
  change _ < 2*detectorConstant*(M x (tallest x))^17
  rw [Nat.mul_assoc]
  exact combine_heights big roots (physical_scale_heights dom).2.2 bound

/-- The former three-comparison condition always supplies a sufficient single frame. -/
noncomputable def select_from_full {x : Fin 84→Rat} (g : FullArithmetic x) : SelectedArithmetic x := by
  let f:=maximumFrame (M x)
  let V:=detectorConstant*(M x f)^17
  have bound (i : Scale) : comparisonBound x i ≤ V+2 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_maximum (M x) i) 17)) 2
  have top:=three_max (P:=fun k=>k≤V+2) (bound .first) (bound .second) (bound .third)
  have mid:=Nat.le_trans g.abscissas (Nat.add_le_add_left (Nat.mul_le_mul_left 3 top) 15)
  have pos:=Nat.pow_pos (scale_radical_pos x f) (n:=17)
  have hi : 32≤V := Nat.le_trans (by decide +kernel : 32≤detectorConstant)
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left detectorConstant pos)
  refine ⟨g.labels,f,?_,?_,Or.inr ⟨fun p hp=>⟨g.scalarMultiplier,g.scalarCharts p hp⟩,g.scalarHeight⟩,
    g.oddFirst,g.lastNonzero,g.anchorNonzero,g.anchor⟩
  · have charts {i} (a : FullFrame x i g.labels) : ComparisonCharts x i g.labels :=
      fun p hp=>⟨a.multiplier,a.charts p hp⟩
    have all (i : Scale) : ComparisonCharts x i g.labels := by
      cases i with
      | first=>exact charts g.first
      | second=>exact charts g.second
      | third=>exact charts g.third
    exact all f
  · change _ < (2*detectorConstant)*(M x f)^17
    rw [Nat.mul_assoc]
    change _ < 2*V
    omega

#print axioms physical_scale_heights
#print axioms root_bound_at_tallest
#print axioms select_from_full
end HeightSpecialization
