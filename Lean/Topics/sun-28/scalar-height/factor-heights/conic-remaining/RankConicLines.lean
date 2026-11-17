import HomogeneousQuartics
import OcticExclusion

namespace Sun28.ConicRemaining
open Sun28.ScalarRankZero Sun28.FactorHeights Sun28.OcticResidues
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

def e₁ (j:Fin 3):ℤ := ![2,77,154] j
def a₁ (j:Fin 3):ℤ := ![-57,-4,-8] j
def b₁ (j:Fin 3):ℤ := ![7,1,3] j
def z₁ (j:Fin 3):ℤ := ![1733,6,8] j
def support₁ (j:Fin 3):ℕ := ![3073,3073,9219] j
def f₁ (j:Fin 3)(u v:ℤ):ℤ := a₁ j*u^2-2*z₁ j*u*v+(e₁ j*a₁ j+735*b₁ j)*v^2
def g₁ (j:Fin 3)(u v:ℤ):ℤ := b₁ j*(u^2-e₁ j*v^2)

private theorem nsq (j:Fin 3) : ¬IsSquare (e₁ j) ∧ ¬IsSquare (134288/e₁ j:ℤ) := by
  fin_cases j <;> norm_num [e₁,a₁,b₁,z₁]

private theorem line {e a b z c t w:ℚ} (bn:b≠0) (hn:t^2≠a/b)
    (base:z^2=e*a^2+735*a*b+c*b^2) (eq:w^2=e*t^4+735*t^2+c) :
    ∃l:ℚ, b*(l^2-e)*t^2=a*l^2-2*z*l+(e*a+735*b) := by
  let l:ℚ:=(w-z/b)/(t^2-a/b)
  have slopes: w=z/b+l*(t^2-a/b) := by dsimp[l];rw[div_mul_cancel₀ _ (sub_ne_zero.mpr hn)];ring
  have d:(t^2-a/b)*(b*(l^2-e)*t^2-(a*l^2-2*z*l+(e*a+735*b)))=0 := by
    calc
      _ = b*((z/b+l*(t^2-a/b))^2-e*t^4-735*t^2-c)-b*((z/b)^2-e*(a/b)^2-735*(a/b)-c) := by field_simp[bn];ring
      _ = 0 := by rw[←slopes,eq];field_simp[bn];linear_combination -base
  exact ⟨l,sub_eq_zero.mp ((mul_eq_zero.mp d).resolve_left (sub_ne_zero.mpr hn))⟩

/-- A rational point on each quartic gives a common squareclass on two explicit binary quadratics. -/
theorem to_line (j:Fin 3) (rep:represented 735 134288 (e₁ j)) :
    ∃u v:ℤ, u.natAbs.Coprime v.natAbs ∧ f₁ j u v≠0 ∧ IsSquare (f₁ j u v*g₁ j u v) := by
  obtain ⟨U,V,Z,guard,eq⟩:=(represented_iff_projective ..).mp rep
  have en:¬IsSquare ((e₁ j:ℤ):ℚ):=fun h=>(nsq j).1 (Rat.isSquare_intCast_iff.mp h)
  have cn:¬IsSquare ((134288/e₁ j:ℤ):ℚ):=fun h=>(nsq j).2 (Rat.isSquare_intCast_iff.mp h)
  have vn:V≠0:=by
    intro hz;obtain un|vn:=guard
    · apply en;refine ⟨Z/U^2,?_⟩;rw[hz] at eq;simp [quartic] at eq;field_simp[un];linear_combination -eq
    · exact vn hz
  let t:=U/V
  have eq':(Z/V^2)^2=(e₁ j:ℚ)*t^4+735*t^2+(134288/e₁ j:ℤ) := by
    dsimp[t];unfold quartic at eq;field_simp[vn];linear_combination eq
  have tn:t≠0:=by
    intro hz;apply cn;refine ⟨Z/V^2,?_⟩;rw[hz] at eq';simpa [sq] using eq'.symm
  have bp:(0:ℚ)<b₁ j:=by fin_cases j <;> norm_num [e₁,a₁,b₁,z₁]
  have ap:(a₁ j:ℚ)<0:=by fin_cases j <;> norm_num [e₁,a₁,b₁,z₁]
  have base:(z₁ j:ℚ)^2=(e₁ j:ℚ)*(a₁ j:ℚ)^2+735*(a₁ j:ℚ)*(b₁ j:ℚ)+(134288/e₁ j:ℤ)*(b₁ j:ℚ)^2 := by
    fin_cases j <;> norm_num [e₁,a₁,b₁,z₁]
  obtain ⟨l,hl⟩:=line bp.ne' (ne_of_gt (lt_of_lt_of_le (div_neg_of_neg_of_pos ap bp) (sq_nonneg t))) base eq'
  let u:=l.num
  let v:ℤ:=l.den
  have v0:(v:ℚ)≠0:=by dsimp[v];exact_mod_cast l.den_nz
  have hv:(u:ℚ)=l*v:=by dsimp[u,v];exact (div_eq_iff (by exact_mod_cast l.den_nz)).mp l.num_div_den
  have coeff: (f₁ j u v:ℚ)=(g₁ j u v:ℚ)*t^2 := by
    unfold f₁ g₁;push_cast;rw[hv];linear_combination -(v:ℚ)^2*hl
  have gn:(g₁ j u v:ℚ)≠0 := by
    intro gh;apply en;refine ⟨l,?_⟩;unfold g₁ at gh;push_cast at gh;rw[hv] at gh
    have h1: (l*(v:ℚ))^2-(e₁ j:ℚ)*(v:ℚ)^2=0 := (mul_eq_zero.mp gh).resolve_left bp.ne'
    have h2: (l^2-(e₁ j:ℚ))*(v:ℚ)^2=0:=by linear_combination h1
    simpa only [pow_two] using (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right (pow_ne_zero 2 v0))).symm
  refine ⟨u,v,by simpa [u,v] using l.reduced,?_,?_⟩
  · intro hz;have hh:(f₁ j u v:ℚ)=0:=by exact_mod_cast hz
    exact (mul_ne_zero gn (pow_ne_zero 2 tn)) (coeff ▸ hh)
  · apply Rat.isSquare_intCast_iff.mp;refine ⟨(g₁ j u v:ℚ)*t,?_⟩
    push_cast;rw[coeff];ring

end Sun28.ConicRemaining
#print axioms Sun28.ConicRemaining.to_line
