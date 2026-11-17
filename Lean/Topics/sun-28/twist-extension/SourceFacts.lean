import PreparedProducts
import AffineSurface

namespace Sun28.TwistExtension
open PreparedPoles PairedClasses TwistRank
noncomputable section

/-- The representation of d by the first two conics gives an explicit norm
d=N((k+√β)(3k+√β)/h). Norms multiply when two factors are joined. -/
theorem family_norm {β d : ℕ} (f : Family β d) :
    ∃ a b : ℚ, (d:ℚ)=a^2-(β:ℚ)*b^2 := by
  obtain ⟨k,h,hn,e⟩:=f
  refine ⟨(3*k^2+β)/h,4*k/h,?_⟩
  field_simp
  linear_combination -e

theorem product_norm {β d e : ℕ} (f : Family β d) (g : Family β e) :
    ∃ a b : ℚ, ((d*e:ℕ):ℚ)=a^2-(β:ℚ)*b^2 := by
  obtain ⟨r,s,h⟩:=family_norm f
  obtain ⟨u,v,k⟩:=family_norm g
  refine ⟨r*u+β*s*v,r*v+s*u,?_⟩
  rw [Nat.cast_mul,h,k];ring

/-- Every positive nonsquare represented by the norm yields a rational
point of the requested norm conic with both coordinates nonzero. -/
theorem norm_conic {β θ : ℕ} (bp : 0<β) (tp : 0<θ) (sf : Squarefree θ) (big : 1<θ)
    (h : ∃ r s : ℚ, (θ:ℚ)=r^2-(β:ℚ)*s^2) : NormConic β θ := by
  obtain ⟨r,s,e⟩:=h
  have t : 0<(θ:ℚ):=by exact_mod_cast tp
  have b : 0≤(β:ℚ):=by positivity
  have rn : r≠0:=by rintro rfl; nlinarith only [e,t,mul_nonneg b (sq_nonneg s)]
  have sn : s≠0:=by
    intro zero
    have eq:(θ:ℚ)=(1:ℤ)*r^2:=by simpa only [zero,zero_pow two_ne_zero,mul_zero,sub_zero,Int.cast_one,one_mul] using e
    have v:=ZInQ.RouteK.sqf_eq_of_eq_mul_sq (d:=(1:ℤ)) squarefree_one rn eq
    have w:=ZInQ.RouteK.sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr sf) (t:=(1:ℚ)) one_ne_zero
      (show (θ:ℚ)=(θ:ℤ)*(1:ℚ)^2 by simp)
    have same : θ=1:=by exact_mod_cast w.symm.trans v
    omega
  refine ⟨s/r,1/r,div_ne_zero sn rn,div_ne_zero one_ne_zero rn,?_⟩
  field_simp
  linear_combination e

theorem prepared_products {β : ℕ} (bp : 0<β) (bs : Squarefree β) (b6 : β.Coprime 6)
    (bm : β%24=17) : ∃ d : ℕ, 1<d ∧ ∀ B : ℕ, ∃ e : ℕ, B<d*e ∧ 1<e ∧
    d.Coprime e ∧ AdmissiblePair β (d*e) ∧ FixedSquares (d*e) ∧ NormConic β (d*e) ∧
    FactorPair β (d*e) ∧ AffineSurface (β:ℚ) ((d*e:ℕ):ℚ) ∧ ¬(β*d).Coprime (d*e) := by
  obtain ⟨d,dp,vary⟩:=unbounded_products bp bs b6 bm
  refine ⟨d,dp,?_⟩
  intro B
  obtain ⟨e,eb,ep,c,adm,fp,f,g,pair,surf,bad⟩:=vary B
  have enough : 1<d*e:=lt_of_lt_of_le ep (by simpa only [one_mul] using Nat.mul_le_mul_right e dp.le)
  exact ⟨e,eb,ep,c,adm,fp,norm_conic bp adm.2.1 adm.2.2.2.1 enough (product_norm f g),pair,
    affine_iff_surface.mpr surf,bad⟩

end
end Sun28.TwistExtension
#print axioms Sun28.TwistExtension.family_norm
#print axioms Sun28.TwistExtension.product_norm
#print axioms Sun28.TwistExtension.norm_conic
#print axioms Sun28.TwistExtension.prepared_products
