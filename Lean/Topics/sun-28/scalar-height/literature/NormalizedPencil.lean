import ScalarEstimates
import PartialPencil

namespace Sun28.ScalarPencil
open Sun28.WitnessHeight Sun28.ScalarHeight Sun28.Ordinary Sun28.FiveMarkUnits
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQ.RouteK Height
open private fraction_support from PartialPencil
noncomputable section

/-- Inverting u in the reduced scalar input a/b=(u c)/b produces a
simultaneous Pell system with constants independent of u and b. -/
theorem rational_pencil {x:ℚ} {u c:ℤ} (nonzero:x≠0) (split:x.num=u*c) :
    let A:=(beta x).num
    let B:ℤ:=(beta x).den
    let T:=heightRadical A B
    let P:=u.natAbs.primeFactors
    ∃ (h k:ℤ) (X Y Z:ℚ), h≠0 ∧ k≠0 ∧
      (6:ℤ).natAbs.primeFactors⊆support A B ∧ h.natAbs.primeFactors⊆support A B ∧
      k.natAbs.primeFactors⊆support A B ∧
      (6:ℕ)≤2^32*T ∧ h.natAbs≤2^32*T ∧ k.natAbs≤2^32*T ∧
      X.den.primeFactors⊆P ∧ Y.den.primeFactors⊆P ∧ Z.den.primeFactors⊆P ∧
      6*X^2-(h:ℚ)*Y^2=((-4*c^2:ℤ):ℚ) ∧
      6*X^2-(k:ℚ)*Z^2=((-6*c^2:ℤ):ℚ) ∧ x=(c:ℚ)/X := by
  dsimp only
  obtain ⟨h,k,v,w,nh,nk,s₀,s₁,s₂,b₀,b₁,b₂,e₁,e₂⟩:=data x
  have an:=Rat.num_ne_zero.mpr nonzero
  have un:u≠0:=by intro z;simp [z] at split;exact nonzero split
  have uq:(u:ℚ)≠0:=by exact_mod_cast un
  have bn:(x.den:ℚ)≠0:=by exact_mod_cast x.den_nz
  rw [split] at e₁ e₂
  refine ⟨h,k,(x.den:ℚ)/u,(v:ℚ)/u,(w:ℚ)/u,nh,nk,s₀,s₁,s₂,b₀,b₁,b₂,
    ?_,fraction_support v u un,fraction_support w u un,?_,?_,?_⟩
  · simpa only [Int.cast_natCast] using fraction_support (x.den:ℤ) u un
  · have eq:(6:ℚ)*(x.den:ℚ)^2-(h:ℚ)*(v:ℚ)^2= -4*((u:ℚ)*(c:ℚ))^2:=by exact_mod_cast e₁
    push_cast
    field_simp
    linear_combination eq
  · have eq:(6:ℚ)*(x.den:ℚ)^2-(k:ℚ)*(w:ℚ)^2= -6*((u:ℚ)*(c:ℚ))^2:=by exact_mod_cast e₂
    push_cast
    field_simp
    linear_combination eq
  · calc
      x=(x.num:ℚ)/x.den:=x.num_div_den.symm
      _=(c:ℚ)/((x.den:ℚ)/u):=by rw [split];push_cast;field_simp

end
end Sun28.ScalarPencil
#print axioms Sun28.ScalarPencil.rational_pencil
