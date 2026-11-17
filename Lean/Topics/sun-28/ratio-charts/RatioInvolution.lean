import ConductorProjection28

namespace Sun28.PointLifts
noncomputable section

theorem swap_conics {b θ s z h j : ℚ} (tn : θ≠0) (F : ConicFibre b θ s z h j) :
    ConicFibre b θ (θ/s) (s^2/θ*z) j h := by
  refine ⟨div_ne_zero tn F.s_ne,mul_ne_zero (div_ne_zero (pow_ne_zero _ F.s_ne) tn) F.z_ne,F.second,?_⟩
  have flip : (θ/s)^2/θ*(s^2/θ*z)=z := by field_simp [F.s_ne]
  rw [flip];exact F.first

theorem ratio_involution {b θ s : ℚ} (bp : 0<b) (tn : θ≠0) (sn : s≠0) :
    SingleFibre b θ s ↔ SingleFibre b θ (θ/s) := by
  have swap {t : ℚ} (n : t≠0) (H : SingleFibre b θ t) : SingleFibre b θ (θ/t) := by
    obtain ⟨z,h,j,F⟩ := (conics_iff_single bp tn n).mpr H
    exact (conics_iff_single bp tn (div_ne_zero tn n)).mp ⟨_,_,_,swap_conics tn F⟩
  refine ⟨swap sn,fun H=>?_⟩
  have eq : θ/(θ/s)=s := by field_simp
  simpa only [eq] using swap (div_ne_zero tn sn) H

theorem principal_ratio {b θ : ℚ} (bp : 0<b) (tp : 0<θ) (none : ¬PrescribedPoints.OneQuartic b θ)
    {s : ℚ} (sn : s≠0) (H : SingleFibre b θ s) :
    ∃ t : ℚ, 0<t ∧ t^2<θ ∧ SingleFibre b θ t := by
  have hn : |s|^2=s^2 := sq_abs s
  have pos := abs_pos.mpr sn
  have fibre : SingleFibre b θ |s| := by simpa [SingleFibre,singlePolynomial,hn] using H
  have neq : |s|^2≠θ := by
    intro e
    apply none
    exact ⟨1,0,|s|,Or.inl (by simpa [PairedClasses.quartic] using e.symm)⟩
  rcases lt_or_gt_of_ne neq with lt|gt
  · exact ⟨_,pos,lt,fibre⟩
  · refine ⟨θ/|s|,div_pos tp pos,?_,(ratio_involution bp tp.ne' pos.ne').mp fibre⟩
    rw [div_pow,div_lt_iff₀ (sq_pos_of_pos pos),sq θ]
    exact mul_lt_mul_of_pos_left gt tp

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.swap_conics
#print axioms Sun28.PointLifts.ratio_involution
#print axioms Sun28.PointLifts.principal_ratio
