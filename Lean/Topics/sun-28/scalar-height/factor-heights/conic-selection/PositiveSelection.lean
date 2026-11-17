import SquarefreeFactors
import MarkedCells
import PhysicalSelection

namespace Sun28.ConicSelection
open Sun28.ConicCovers Sun28.ConicArithmetic Sun28.OcticResidues
noncomputable section
set_option maxHeartbeats 800000
set_option linter.unnecessarySimpa false

theorem rational_representative {s:ℚ} (f:Factors s) {d:ℕ} (ds:d∈(7194:ℕ).divisors) {u v:ℤ}
    (P:f.P=(d:ℤ)*u^2) (Q:f.Q=(((7194:ℕ)/d:ℕ):ℤ)*v^2) (uv:u*v=f.b^2) :
    imaginaryClass (-14*(d:ℚ)) s := by
  let e:=7194/d
  have deZ : d*e=7194 := Nat.mul_div_cancel' (Nat.mem_divisors.mp ds).1
  have de : (d:ℚ)*(e:ℚ)=7194:=by exact_mod_cast deZ
  have dn : (d:ℚ)≠0 := by intro h;rw [h] at de; norm_num at de
  have bn : (f.b:ℚ)≠0 := by exact_mod_cast f.bpos.ne'
  have xy : (u:ℚ)*(v:ℚ)=(f.b:ℚ)^2 := by exact_mod_cast uv
  have eqZ:=f.diff
  rw [P,Q] at eqZ
  have eqQ : (e:ℚ)*(v:ℚ)^2-(d:ℚ)*(u:ℚ)^2=686*(f.a:ℚ)^2-349*(f.b:ℚ)^2 := by exact_mod_cast eqZ
  rw [←f.slope] at eqQ
  refine ⟨(u:ℚ)/(98*(f.b:ℚ)),(v:ℚ)/(98*(d:ℚ)*(f.b:ℚ)),?_,?_⟩
  · field_simp [bn,dn]
    linear_combination -9604*(d:ℚ)*eqQ+9604*(v:ℚ)^2*de
  · field_simp [bn,dn]
    linear_combination 9604*xy

/-- The physical positive marked fibre needs only the two rational congruences at 2 and 7. -/
theorem positive_selmer_selection : PositiveSelmerSelection := by
  intro s y rng sq sz sw _ curve
  obtain ⟨r,hr⟩:=sq
  obtain ⟨v,hv⟩:=sz
  obtain ⟨w,hw⟩:=sw
  obtain ⟨f⟩:=physical_factors rng hr hv hw (by simpa [quintic] using curve)
  obtain ⟨d,ds,U,V,hP,hQ,mul⟩:=four_factors f
  have clazz:=rational_representative f ds hP hQ mul
  rcases at_two_seven f ds hP hQ mul with rfl|rfl
  · right; convert clazz using 1; norm_num
  · obtain ⟨u,v,real,imag⟩:=clazz
    left; refine ⟨2*u,2*v,?_,?_⟩
    · push_cast at real; linear_combination real
    · push_cast at imag; linear_combination imag

end
end Sun28.ConicSelection
#print axioms Sun28.ConicSelection.rational_representative
#print axioms Sun28.ConicSelection.positive_selmer_selection