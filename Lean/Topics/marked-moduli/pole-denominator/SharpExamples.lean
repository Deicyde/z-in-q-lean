import ParameterReturn

/-! Primitive parameters approaching the optimal coefficient in the height comparison. -/
namespace ZInQBlueprint.PoleNorm
open ZInQ
noncomputable section

def testParameter (n : ℕ) : ℚ :=
  let q : ℤ := 120*(n:ℤ)+2
  (-120*q:ℤ)/(5*q-3:ℤ)

private theorem primitive_test (n : ℕ) :
    let q : ℤ := 120*(n:ℤ)+2
    IsCoprime (-120*q) (5*q-3) := by
  let q : ℤ := 120*(n:ℤ)+2
  change IsCoprime (-120*q) (5*q-3)
  apply IsCoprime.mul_left
  · refine ⟨-(1+85*(n:ℤ)),-17,?_⟩
    dsimp [q]
    ring
  · refine ⟨2-5*(80*(n:ℤ)+1),80*(n:ℤ)+1,?_⟩
    dsimp [q]
    ring

theorem test_coordinates (n : ℕ) :
    let q : ℤ := 120*(n:ℤ)+2
    let u := testParameter n
    u.num= -120*q ∧ (u.den:ℤ)=5*q-3 ∧
    (parameter u).num=3 ∧ ((parameter u).den:ℤ)=q ∧ denominatorRoot u=q^2+3 := by
  let q : ℤ := 120*(n:ℤ)+2
  let u := testParameter n
  have hQ : q>0 := by dsimp [q]; positivity
  have hB : 0<5*q-3 := by dsimp [q]; omega
  have cop : (-120*q).natAbs.Coprime (5*q-3).natAbs := Int.isCoprime_iff_gcd_eq_one.mp (primitive_test n)
  have hn : u.num= -120*q := Rat.num_div_eq_of_coprime hB cop
  have hd : (u.den:ℤ)=5*q-3 := Rat.den_div_eq_of_coprime hB cop
  have hparam : parameter u = (3:ℚ)/q := by
    change 5+120/(((-120*q:ℤ):ℚ)/((5*q-3:ℤ):ℚ))=_
    push_cast
    have hq : (q:ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    have hb : 5*(q:ℚ)-3 ≠ 0 := by exact_mod_cast hB.ne'
    field_simp [hq,hb]
    ring
  have comp : IsCoprime (3:ℤ) q := ⟨40*(n:ℤ)+1,-1,by dsimp [q]; ring⟩
  have hp : (parameter u).num=3 := hparam ▸ Rat.num_div_eq_of_coprime (a:=3) hQ (Int.isCoprime_iff_gcd_eq_one.mp comp)
  have hden : ((parameter u).den:ℤ)=q := hparam ▸ Rat.den_div_eq_of_coprime (a:=3) hQ (Int.isCoprime_iff_gcd_eq_one.mp comp)
  refine ⟨hn,hd,hp,hden,?_⟩
  change norm (parameter u).num (parameter u).den / factor (parameter u).num (parameter u).den = q^2+3
  rw [hp,hden]
  have evenq : q%2=0 := by dsimp [q]; omega
  simp [norm,factor,dyadicFactor,triadicFactor,evenq]
  omega

/-- The exact quotient on an unbounded family of inputs, including the error term. -/
theorem test_height_ratio (n : ℕ) :
    let u := testParameter n
    u ≠ 0 ∧ (max |u.num| (u.den:ℤ))^2 = 14400*denominatorRoot u - 43200 := by
  obtain ⟨hn,hd,_,_,h⟩ := test_coordinates n
  dsimp only at hn hd h ⊢
  let q : ℤ := 120*(n:ℤ)+2
  have hp : 0<q := by dsimp [q]; positivity
  change (testParameter n).num= -120*q at hn
  refine ⟨?_,?_⟩
  · intro hzero
    rw [hzero] at hn
    simp at hn
    omega
  · rw [hn,hd,h]
    change (max (abs (-120*q)) (5*q-3))^2=14400*(q^2+3)-43200
    rw [abs_of_neg (by omega),max_eq_left (by omega)]
    ring

end
end ZInQBlueprint.PoleNorm
#print axioms ZInQBlueprint.PoleNorm.test_coordinates
#print axioms ZInQBlueprint.PoleNorm.test_height_ratio
