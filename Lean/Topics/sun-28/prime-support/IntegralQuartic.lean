import ThreeAdicRatio

namespace Sun28.PointLifts
noncomputable section

/-- The two even binary quadratics obtained after clearing the ratio n/m. -/
def leftForm {R : Type*} [CommRing R] (b a d U V : R) : R :=
  (a-d)*U^2+(3*a+d)*b*V^2

def rightForm {R : Type*} [CommRing R] (b a d U V : R) : R :=
  (a+3*d)*U^2+3*(a-d)*b*V^2

/-- The exact change of model, with ordinate Y=b m² W. -/
theorem cleared_quartic (b θ n m U V W : ℚ) (bn : b≠0) (mn : m≠0) :
    b*W^2=singlePolynomial b θ (n/m) U V ↔
      (b*m^2*W)^2 = b*leftForm b (n^2) (θ*m^2) U V * rightForm b (n^2) (θ*m^2) U V := by
  unfold singlePolynomial leftForm rightForm
  constructor <;> intro eqn
  · field_simp at eqn
    linear_combination b*eqn
  · field_simp
    apply mul_left_cancel₀ bn
    linear_combination eqn

private theorem primitive_direction {u v : ℚ} (nz : u≠0 ∨ v≠0) :
    ∃ (U V : ℤ) (c : ℚ), U.natAbs.Coprime V.natAbs ∧ c≠0 ∧ u=U*c ∧ v=V*c := by
  by_cases vn : v=0
  · subst v
    exact ⟨1,0,u,by simp,nz.resolve_right (by simp),by simp,by simp⟩
  · let t:=u/v
    have dn : (t.den:ℚ)≠0 := by exact_mod_cast t.den_ne_zero
    have num : (t.num:ℚ)=t*t.den := ((eq_div_iff dn).mp (Rat.num_div_den t).symm).symm
    refine ⟨t.num,(t.den:ℤ),v/t.den,by simpa using t.reduced,div_ne_zero vn dn,?_,?_⟩
    · rw [num];dsimp [t];field_simp
    · push_cast;field_simp

def IntegralFibre (b θ n m : ℤ) : Prop := ∃ U V Y : ℤ,
  U.natAbs.Coprime V.natAbs ∧ U^2-b*V^2≠0 ∧
  Y^2=b*leftForm b (n^2) (θ*m^2) U V * rightForm b (n^2) (θ*m^2) U V

/-- Every physical quartic point can be scaled to a primitive integer
direction; its normalized ordinate is then integral. Conversely every such
triple gives the original rational witness, including a zero ordinate. -/
theorem single_iff_integral {b θ n m : ℤ} (bn : b≠0) (mn : m≠0) :
    SingleFibre b θ ((n:ℚ)/m) ↔ IntegralFibre b θ n m := by
  have B : (b:ℚ)≠0 := by exact_mod_cast bn
  have M : (m:ℚ)≠0 := by exact_mod_cast mn
  constructor
  · rintro ⟨u,v,W,uv,L,point⟩
    obtain ⟨U,V,c,prim,cn,hu,hv⟩ := primitive_direction uv
    let F : ℤ := b*leftForm b (n^2) (θ*m^2) U V * rightForm b (n^2) (θ*m^2) U V
    have raw := (cleared_quartic b θ n m u v W B M).mp point
    rw [hu,hv] at raw L
    have scale : ((b*m^2*W)/c^2)^2=(F:ℚ) := by
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero _ (pow_ne_zero 2 cn))).mpr
      dsimp [F,leftForm,rightForm] at raw ⊢
      push_cast
      linear_combination raw
    have sq : IsSquare (F:ℚ) := ⟨_,by simpa [pow_two] using scale.symm⟩
    obtain ⟨Y,hy⟩ := Rat.isSquare_intCast_iff.mp sq
    refine ⟨U,V,Y,prim,?_,by simpa only [F,pow_two] using hy.symm⟩
    intro zero
    have zero' : (U:ℚ)^2-(b:ℚ)*V^2=0 := by exact_mod_cast zero
    apply L
    linear_combination c^2*zero'
  · rintro ⟨U,V,Y,prim,L,eqn⟩
    have L' : (U:ℚ)^2-(b:ℚ)*V^2≠0 := by exact_mod_cast L
    have uv : (U:ℚ)≠0 ∨ (V:ℚ)≠0 := by
      by_contra! both
      simp [both.1,both.2] at L'
    refine ⟨U,V,(Y:ℚ)/(b*m^2),uv,L',(cleared_quartic _ _ _ _ _ _ _ B M).mpr ?_⟩
    have F : (Y:ℚ)^2=(b:ℚ)*leftForm (b:ℚ) ((n:ℚ)^2) (θ*(m:ℚ)^2) U V *
        rightForm (b:ℚ) ((n:ℚ)^2) (θ*(m:ℚ)^2) U V := by
      unfold leftForm rightForm at *
      exact_mod_cast eqn
    rw [mul_comm (b*m^2:ℚ),div_mul_cancel₀ _ (mul_ne_zero B (pow_ne_zero 2 M))]
    exact F

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.cleared_quartic
#print axioms Sun28.PointLifts.single_iff_integral
