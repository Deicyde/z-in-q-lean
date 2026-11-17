import DivisorResidues
import QuarticBoundary
import RatioInvolution

namespace Sun28.PointLifts
open Sun28.PrescribedPoints Sun28.PairedClasses Sun28.PreparedPoles Sun28.TwistRank
  Sun28.TwistExtension Sun28.PointFibres Sun28.PointDescent
noncomputable section

/-- The two residue tests depend only on the proposed divisor and ratio. -/
def SplitDivisor (b θ n m D : ℤ) : Prop :=
  ∀ p : ℕ, ∀ [Fact p.Prime], (D:ZMod p)=0 →
    (((n:ZMod p)=0 ∧ (θ:ZMod p)*(m:ZMod p)^2≠0) → IsSquare (b:ZMod p)) ∧
    (((θ:ZMod p)*(m:ZMod p)^2=0 ∧ (n:ZMod p)≠0) → IsSquare (-3*(b:ZMod p)))

/-- The conic intersection on the open locus, with no torsion sections. -/
def RegularFibre (b θ n m : ℤ) : Prop :=
  ∃ U V D x y : ℤ, U.natAbs.Coprime V.natAbs ∧ U^2-b*V^2≠0 ∧
    U≠0 ∧ V≠0 ∧ x≠0 ∧ y≠0 ∧ 0<D ∧ Squarefree D ∧ D ∣ 2*b*θ*n*m ∧
    SplitDivisor b θ n m D ∧ leftForm b (n^2) (θ*m^2) U V=D*x^2 ∧
    b*rightForm b (n^2) (θ*m^2) U V=D*y^2

theorem integral_iff_regular {b θ n m : ℤ} (bp : 0<b) (tp : 0<θ)
    (nn : n≠0) (mn : m≠0) (out : ¬OneQuartic (b:ℚ) θ) :
    IntegralFibre b θ n m ↔ RegularFibre b θ n m := by
  constructor
  · rintro ⟨U,V,Y,cop,L,E⟩
    have no (r : U=0 ∨ V=0 ∨ Y=0) : False := out (integral_boundary bp tp nn mn L E r)
    have yn : Y≠0 := fun h=>no (Or.inr (Or.inr h))
    have prod : b*leftForm b (n^2) (θ*m^2) U V*rightForm b (n^2) (θ*m^2) U V≠0 := E ▸ pow_ne_zero 2 yn
    have fn : leftForm b (n^2) (θ*m^2) U V≠0 := by intro e;exact prod (by simp [e])
    have gn : b*rightForm b (n^2) (θ*m^2) U V≠0 := by
      rw [mul_right_comm b _ _] at prod
      exact left_ne_zero_of_mul prod
    obtain ⟨D,x,y,sf,dv,f,g⟩ := finite_descent cop fn gn E
    have pos := positive_left bp (sq_pos_of_ne_zero nn) (mul_pos tp (sq_pos_of_ne_zero mn)) fn gn E
    rw [f] at pos
    refine ⟨U,V,D,x,y,cop,L,fun e=>no (Or.inl e),fun e=>no (Or.inr (Or.inl e)),
      fun e=>fn (by simpa only [e,zero_pow (by decide : 2≠0),mul_zero] using f),fun e=>gn (by simpa only [e,zero_pow (by decide : 2≠0),mul_zero] using g),
      pos_of_mul_pos_left pos (sq_nonneg _),sf,reduced_divisor sf dv,fun p _ pd=>divisor_root_tests cop f pd,f,g⟩
  · rintro ⟨U,V,D,x,y,cop,L,_,_,_,_,_,_,_,_,f,g⟩
    exact ⟨U,V,D*x*y,cop,L,by rw [mul_right_comm b _ _,g,f];ring⟩

theorem single_iff_regular {b θ : ℕ} (bp : 0<b) (tp : 0<θ) {s : ℚ} (sn : s≠0)
    (out : ¬OneQuartic (b:ℚ) θ) : SingleFibre b θ s ↔ RegularFibre b θ s.num s.den := by
  have h:= (single_iff_integral (b:=(b:ℤ)) (θ:=(θ:ℤ)) (n:=s.num) (m:=(s.den:ℤ))
    (by exact_mod_cast bp.ne') (by exact_mod_cast s.den_ne_zero)).trans
    (integral_iff_regular (by exact_mod_cast bp) (by exact_mod_cast tp) (Rat.num_ne_zero.mpr sn)
      (by exact_mod_cast s.den_ne_zero) out)
  simpa only [Int.cast_natCast,Rat.num_div_den] using h

def RegularResidual : Prop := ∀ b θ : ℕ, AdmissiblePair b θ → InputClass b → FixedSquares θ →
  NormConic b θ → ¬FactorPair b θ → ¬OneQuartic (b:ℚ) (θ:ℚ) →
  (∀ t : ℚ, t≠0 → ¬RatioCover (b:ℚ) (θ:ℚ) t) →
  ∃ s : ℚ, 0<s ∧ s^2<θ ∧ AllowedRatio b θ s ∧ padicValRat 3 s=0 ∧ RegularFibre b θ s.num s.den

theorem residual_iff_regular : LocalRatioResidual ↔ RegularResidual := by
  constructor
  · intro h b θ a i f N c o t
    obtain ⟨s,r,F⟩:=h b θ a i f N c o t
    obtain ⟨k,pos,short,G⟩:=principal_ratio (by exact_mod_cast a.1) (by exact_mod_cast a.2.1) o r.1 F
    exact ⟨k,pos,short,allowed_of_fibre a pos.ne' G,three_unit_of_fibre a pos.ne' G,
      (single_iff_regular a.1 a.2.1 pos.ne' o).mp G⟩
  · intro h b θ a i f N c o t
    obtain ⟨s,pos,_,r,_,F⟩:=h b θ a i f N c o t
    exact ⟨s,r,(single_iff_regular a.1 a.2.1 pos.ne' o).mpr F⟩

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.integral_iff_regular
#print axioms Sun28.PointLifts.single_iff_regular
#print axioms Sun28.PointLifts.residual_iff_regular
