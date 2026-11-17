import PrescribedProjection

namespace Sun28.PrescribedPoints
open PairedClasses PreparedPoles TwistExtension TwistRank
open private zero_twist restore from SignedSections
noncomputable section

def ZeroPair (b θ : ℚ) : Prop := ∃ l u v y z : ℚ,
  l≠0 ∧ u≠0 ∧ v≠0 ∧ (y=0 ∨ z=0) ∧
  y^2=(b*u^2)*(b*u^2-l)*(b*u^2+3*l) ∧
  z^2=(b*v^2)*(b*v^2-l*θ)*(b*v^2+3*(l*θ))

theorem zero_pair_iff_one {b θ : ℚ} (bp : 0<b) (tn : θ≠0) :
    ZeroPair b θ ↔ OneQuartic b θ := by
  rw [one_quartic_iff bp tn]
  constructor
  · rintro ⟨l,u,v,y,z,_,un,vn,yz,one,two⟩
    rcases yz with yz|zz
    · subst y
      obtain ⟨r,rn,e|e⟩:=zero_twist bp.ne' un one
      · exact Or.inl (restore rn e ⟨v,z,vn,two⟩)
      · exact Or.inr (restore rn e ⟨v,z,vn,two⟩)
    · subst z
      have swap : Point b ((l*θ)*θ) := by
        have pt := point_scale tn (show Point b l from ⟨u,y,un,one⟩)
        convert pt using 1;ring
      obtain ⟨r,rn,e|e⟩:=zero_twist bp.ne' vn two
      · exact Or.inl (restore rn e swap)
      · exact Or.inr (restore rn e swap)
  · rintro (⟨v,z,vn,two⟩|⟨v,z,vn,two⟩)
    · exact ⟨b,1,v,0,z,bp.ne',one_ne_zero,vn,Or.inl rfl,by ring,two⟩
    · exact ⟨-3*b,3,v,0,z,mul_ne_zero (by norm_num) bp.ne',by norm_num,vn,Or.inl rfl,by ring,two⟩

def CoreResidual : Prop := ∀ b θ : ℕ, AdmissiblePair b θ → InputClass b → FixedSquares θ →
  NormConic b θ → ¬FactorPair b θ → ¬OneQuartic (b:ℚ) (θ:ℚ) → NonzeroPair (b:ℚ) (θ:ℚ)

theorem one_of_factor {b θ : ℕ} (bp : 0<b) (tp : 0<θ) (f : Factor b θ) :
    OneQuartic (b:ℚ) (θ:ℚ) :=
  (one_quartic_iff (by exact_mod_cast bp) (by exact_mod_cast tp.ne')).mpr (Or.inl (factor_point bp tp f))

theorem core_iff_residual : CoreResidual ↔ TwistExtension.Residual := by
  rw [residual_iff_live]
  constructor
  · intro core b t a inp fixed n _ _ _ pair test
    exact core b t a inp fixed n pair test
  · intro live b t a inp fixed n pair test
    have ne : t≠1:=by
      rintro rfl
      apply test
      exact ⟨1,0,1,Or.inl (by simp [quartic])⟩
    have no : ¬Factor b t:=fun f=>test (one_of_factor a.1 a.2.1 f)
    exact live b t a inp fixed n ne (fun f=>no (Or.inl f)) (fun f=>no (Or.inr f)) pair test

theorem pole_of_core (core : CoreResidual) {B : ℚ} (ready : ClassPrepared B) :
    Ordinary.polePredicate ScalarHeight.smallMultipliers B := TwistExtension.pole (core_iff_residual.mp core) ready

end
end Sun28.PrescribedPoints
#print axioms Sun28.PrescribedPoints.zero_pair_iff_one
#print axioms Sun28.PrescribedPoints.one_of_factor
#print axioms Sun28.PrescribedPoints.core_iff_residual
#print axioms Sun28.PrescribedPoints.pole_of_core
