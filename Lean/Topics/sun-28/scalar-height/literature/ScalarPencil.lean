import ScalarOctic
import DeepSector

/-! Two integral Pell equations in the denominator of the scalar input. -/
namespace Sun28.ScalarPencil
open Sun28.WitnessHeight Sun28.ScalarHeight Sun28.Ordinary Sun28.FiveMarkUnits
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQ.RouteK
open private sqf_support from ContactPencil
noncomputable section

/-- Multiplying the primitive beta rows by g recovers the unreduced quadratic forms. -/
theorem rows (x:ℚ) :
    let g:ℤ:=Nat.gcd 2 (x.den^2)
    g*(beta x).num=2*x.num^2+3*(x.den:ℤ)^2 ∧
    g*((beta x).num-(beta x).den)=2*x.num^2+2*(x.den:ℤ)^2 := by
  dsimp only
  let a:=x.num
  let b:ℤ:=x.den
  let A:ℤ:=(beta x).num
  let B:ℤ:=(beta x).den
  let g:ℤ:=Nat.gcd 2 (x.den^2)
  have den:B*g=b^2:=by dsimp [B,g,b];exact_mod_cast scalar_denominator x
  have bq : (b:ℚ)≠0:=by dsimp [b];exact_mod_cast x.den_nz
  have ex : x=(a:ℚ)/b := by dsimp [a,b];push_cast;exact x.num_div_den.symm
  have num : (A:ℚ)=beta x*(B:ℚ):=by
    change ((beta x).num:ℚ)=beta x*((beta x).den:ℤ)
    push_cast
    exact (div_eq_iff (Nat.cast_ne_zero.mpr (beta x).den_nz)).mp (beta x).num_div_den
  have rel : (B:ℚ)*(g:ℚ)=(b:ℚ)^2 := by exact_mod_cast den
  have ga : g*A=2*a^2+3*b^2 := by
    apply Int.cast_injective (α:=ℚ)
    push_cast
    rw [num,mul_left_comm,show (g:ℚ)*(B:ℚ)=(b:ℚ)^2 by simpa only [mul_comm] using rel]
    rw [beta,ex]
    field_simp
  change g*A=2*a^2+3*b^2 ∧ g*(A-B)=2*a^2+2*b^2
  exact ⟨ga,by linear_combination ga-den⟩

theorem integer_pencil (x:ℚ) :
    let A:=(beta x).num
    let B:ℤ:=(beta x).den
    let g:ℤ:=Nat.gcd 2 (x.den^2)
    ∃ v w : ℤ, v≠0 ∧ w≠0 ∧
      6*(x.den:ℤ)^2-(2*g*kernel 1 A B)*v^2= -4*x.num^2 ∧
      6*(x.den:ℤ)^2-(3*g*kernel 2 A B)*w^2= -6*x.num^2 := by
  dsimp only
  let A:ℤ:=(beta x).num
  let B:ℤ:=(beta x).den
  let g:ℤ:=Nat.gcd 2 (x.den^2)
  have off:=beta_off_forms x
  obtain ⟨_,v,nv,ev⟩:=sqfInt_spec (off 1)
  obtain ⟨_,w,nw,ew⟩:=sqfInt_spec (off 2)
  change A=kernel 1 A B*v^2 at ev
  change A-B=kernel 2 A B*w^2 at ew
  obtain ⟨h,k⟩:=rows x
  change g*A=2*x.num^2+3*(x.den:ℤ)^2 at h
  change g*(A-B)=2*x.num^2+2*(x.den:ℤ)^2 at k
  refine ⟨v,w,nv,nw,?_,?_⟩
  · change 6*(x.den:ℤ)^2-(2*g*kernel 1 A B)*v^2= -4*x.num^2
    linear_combination 2*g*ev-2*h
  · change 6*(x.den:ℤ)^2-(3*g*kernel 2 A B)*w^2= -6*x.num^2
    linear_combination 3*g*ew-3*k

theorem coefficient_support (x:ℚ) {c:ℤ} {i:Fin 5} (cn:c≠0) (bound:c.natAbs≤6) :
    let A:=(beta x).num
    let B:ℤ:=(beta x).den
    (c*kernel i A B).natAbs.primeFactors⊆support A B := by
  dsimp only
  intro p hp
  let A:ℤ:=(beta x).num
  let B:ℤ:=(beta x).den
  change p∈(c*kernel i A B).natAbs.primeFactors at hp
  have kn : kernel i A B≠0:=(sqfInt_spec (beta_off_forms x i)).1.ne_zero
  rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr cn) (Int.natAbs_ne_zero.mpr kn)] at hp
  rcases Finset.mem_union.mp hp with h|h
  · have le: p≤6:=(Nat.le_of_dvd (Int.natAbs_pos.mpr cn) (Nat.dvd_of_mem_primeFactors h)).trans bound
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),Nat.prime_of_mem_primeFactors h⟩)
  · exact sqf_support (beta_off_forms x) i h

end
end Sun28.ScalarPencil
#print axioms Sun28.ScalarPencil.rows
#print axioms Sun28.ScalarPencil.integer_pencil
#print axioms Sun28.ScalarPencil.coefficient_support
