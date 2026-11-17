import JointSlopeHeight
import ScaleSelection

namespace HeightSpecialization
open IndependentIndices IndependentIndices.Assembly StructuralReduction StructuralReduction.Transfer84
open ProjectionFibres.HeightSupport ProjectionFibres.Comparison WitnessTransfer.Height
set_option exponentiation.threshold 8192

def JointProductHeight (x : Fin 84→Rat) (ns : Labels) :=
  2^(4*(labelSize ns)^2)≤2^30*(jointHeight (atWire x 1249) (atWire x 1252))^3

theorem physical_joint_height {x : Fin 84→Rat} (dom : domain x) :
    (jointHeight (atWire x 1249) (atWire x 1252))^4 ≤ (H (slope x (tallest x)))^5 := by
  obtain ⟨a,b,c⟩:=slope_values x
  have nz : cell x 13≠0 := by
    intro h
    apply noMark x .first dom
    simp [a,h,P]
  apply joint_scale_height nz
  · rw [←a];exact le_maximum (fun f=>H (slope x f)) .first
  · rw [←b];exact le_maximum (fun f=>H (slope x f)) .second
  · rw [←c];exact le_maximum (fun f=>H (slope x f)) .third

private theorem combine_joint {N J U V : Nat} (large : 100<V)
    (first : 2^(4*N^2)≤2^30*J^3) (second : J^4≤U^5) (third : U^2≤2^(4+3*V)) :
    2*N^2<3*V := by
  have bound : 2^(32*N^2)≤2^(300+45*V) := by
    calc
      _=(2^(4*N^2))^8 := by rw [←Nat.pow_mul];congr 1;omega
      _≤(2^30*J^3)^8 := Nat.pow_le_pow_left first 8
      _=2^240*(J^4)^6 := by simp only [Nat.mul_pow,←Nat.pow_mul]
      _≤2^240*(U^5)^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left second 6)
      _=2^240*(U^2)^15 := by simp only [←Nat.pow_mul]
      _≤2^240*(2^(4+3*V))^15 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left third 15)
      _=_ := by rw [←Nat.pow_mul,←Nat.pow_add];congr 1;omega
  have e:=(Nat.pow_le_pow_iff_right (by decide : 1<2)).mp bound
  omega

theorem joint_root_bound {x : Fin 84→Rat} {ns : Labels} (dom : domain x)
    (first : JointProductHeight x ns) (height : SlopeHeight x (tallest x)) :
    2*(labelSize ns)^2<3*(detectorConstant*(M x (tallest x))^17) := by
  have pos:=Nat.pow_pos (scale_radical_pos x (tallest x)) (n:=17)
  have large : 100<detectorConstant*(M x (tallest x))^17 := Nat.lt_of_lt_of_le
    (by decide +kernel : 100<detectorConstant)
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left detectorConstant pos)
  exact combine_joint large first (physical_joint_height dom) height

#print axioms physical_joint_height
#print axioms joint_root_bound
end HeightSpecialization
