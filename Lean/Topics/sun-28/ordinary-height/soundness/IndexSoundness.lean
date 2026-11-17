import SignedLucas
import PublishedHeights

namespace Sun28.Ordinary
open Height NumberField IsDedekindDomain
open scoped NumberField

def scalarStep (n : Fin 4 → ℤ) : ℕ := (n 1-1).natAbs

/-- At the paper's actual multiplier M and a nonzero scalar index q, s=1+Mq
forces c=|s−1|≥M, |s|≥7 and B≥c−1, for either sign of q. -/
theorem scalar_step_range {M : ℕ} (eight : 8 ≤ M) (n : Fin 4 → ℤ) (q : ℤ) (qn : q≠0)
    (anchor : n 1-1=(M:ℤ)*q) :
    M ≤ scalarStep n ∧ 7 ≤ (n 1).natAbs ∧ (scalarStep n:ℝ)-1 ≤ indexSize n ∧
    (scalarStep n:ℝ)-4 ≤ |(n 1:ℝ)|-3 := by
  have plus : (n 1-1).natAbs ≤ (n 1).natAbs+1 := by
    simpa only [sub_eq_add_neg,Int.natAbs_neg,Int.natAbs_one] using Int.natAbs_add_le (n 1) (-1)
  have e : scalarStep n = M*q.natAbs := by
    rw [scalarStep,anchor,Int.natAbs_mul,Int.natAbs_natCast]
  have lower : M ≤ scalarStep n := by
    rw [e]
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr qn)
  have upper : scalarStep n ≤ (n 1).natAbs+1 := plus
  have bnd : |(n 1:ℝ)| ≤ indexSize n := by simp [indexSize]
  have realUpper : (scalarStep n:ℝ) ≤ ((n 1).natAbs:ℝ)+1 := by exact_mod_cast upper
  rw [Nat.cast_natAbs,Int.cast_abs] at realUpper
  exact ⟨lower,by omega,by linarith,by linarith⟩

/-- Full forward implication on the integer indices, before recovering the continuous
witnesses from a compiled polynomial. No growth or congruence between indices is assumed. -/
theorem index_soundness (x : ℚ) (n : Fin 4 → ℤ) (q : ℤ) (qn : q≠0) (zn : n 3≠0)
    {D S : ℝ} (dp : 1 ≤ D) (sc : 0 ≤ S)
    (anchor : n 1-1=(Sun28.multiplier D (numeratorConstant D) S:ℤ)*q)
    (ordinary : lucas (n 1) (n 2) (n 3)≠0 → (indexSize n)^2 ≤ D*
      (1+|((lucas (n 1) (n 2) (n 3):ℤ):ℝ)|^(3/8:ℝ)))
    (num : 2*x^2+3≠(n 0:ℚ) → Real.log (indexSize n) ≤ numeratorConstant D+3*logHeight₁ (2*x^2+3))
    (scalar : logHeight₁ (2*x^2+3) ≤ S*Real.sqrt (scalarStep n:ℝ)) :
    2*x^2+3=(n 0:ℚ) ∧ ∃ k : ℤ, x=(k:ℚ) := by
  let M := Sun28.multiplier D (numeratorConstant D) S
  have eight : 8 ≤ M := (Sun28.multiplier_spec (K:=numeratorConstant D) (zero_le_one.trans dp) sc).2.1
  obtain ⟨mc,big,Bc,cs⟩ := scalar_step_range eight n q qn anchor
  have mcR : (M:ℝ) ≤ (scalarStep n:ℝ) := by exact_mod_cast mc
  obtain ⟨eqn,cut⟩ := actual_cutoff dp sc n mcR Bc ordinary scalar
  have grow := signed_lucas_log (n 1) (n 2) (n 3) zn big eqn
  have power := signed_lucas_power (n 1) (n 2) (n 3) zn big eqn
  have tn : 0 < (n 2).natAbs := (pow_pos (by omega : 0<(n 1).natAbs-1) _).trans_le power
  have pos : (0:ℝ) < |(n 2:ℝ)| := by
    rw [←Int.cast_abs,←Nat.cast_natAbs]
    exact_mod_cast tn
  have size : |(n 2:ℝ)| ≤ indexSize n := by simp [indexSize]
  have logBound := Real.log_le_log pos size
  have equal : 2*x^2+3=(n 0:ℚ) := by
    by_contra wrong
    linarith [num wrong]
  exact ⟨equal,Sun28.integral_input x (n 0) equal⟩

/-- Sun's Proposition 7.3 at the index level. The original five-contact theorem, the
three-scale inequality, the completed local chart, and the scalar height input are explicit. -/
theorem marked_certificate_sound {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    [Algebra.IsQuadraticExtension ℚ K] {ρ : K} (root : ρ^2=2) (σ : K ≃ₐ[ℚ] K) (hs : σ≠1)
    (c h : ℤ) (n m : Fin 4 → ℤ) (x C₀ C₁ η : ℚ) (M : Finset ℚ) (E : Finset ℕ)
    {c₁ c₂ S : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (sc : 0 ≤ S)
    (hh : h≠0) (hc : h-c≠0)
    (outside : ∀ p : ℕ, p.Prime → p ∉ E → 65<p ∧ ¬(p:ℤ) ∣ c ∧ ¬p ∣ separation ∧ ∀ μ ∈ M, padicValRat p μ=0)
    (localChart : ∀ (p : ℕ) [hp : Fact p.Prime], p ∉ E → ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal →
        OrdinaryFormalChart p w)
    (guard : ∀ j, (scaleRoot C₀ C₁ j)^2*η ∉ marks ∧ (scaleRoot C₀ C₁ j)^2*η ≠ 3 ∧ scaleRoot C₀ C₁ j≠0)
    (accepted : ∀ j, let s := scaleRoot C₀ C₁ j; let t := s^2*η
      testTrace root σ c h n m (2*x^2+3) (s^2) t ≠ 0 ∧
        polePredicate M (poleArgument root σ c h n m (2*x^2+3) (s^2) t))
    (upstream : OriginalFiveHeight glazerConstant24 oldCutoff)
    (scale : ∀ H : ℝ, 1 ≤ H → (∀ j, logHeight₁ ((scaleRoot C₀ C₁ j)^2*η) ≤ H) →
      (indexSize n)^2 ≤ c₁*H+c₂)
    (q : ℤ) (qn : q≠0) (zn : n 3≠0)
    (anchor : let D := ordinaryConstant (fiveHeightConstant E) c₁ c₂
      n 1-1=(Sun28.multiplier D (numeratorConstant D) S:ℤ)*q)
    (scalar : logHeight₁ (2*x^2+3) ≤ S*Real.sqrt (scalarStep n:ℝ)) :
    2*x^2+3=(n 0:ℚ) ∧ ∃ k : ℤ, x=(k:ℚ) := by
  have D1 : 1 ≤ ordinaryConstant (fiveHeightConstant E) c₁ c₂ := by
    have H : 1 ≤ fiveHeightConstant E := le_max_left _ _
    unfold ordinaryConstant
    nlinarith [mul_nonneg hc₁ (zero_le_one.trans H)]
  obtain ⟨ord,_,num⟩ := marked_heights_from_glazer root σ hs c h n m (2*x^2+3) C₀ C₁ η M E
    hc₁ hc₂ hh hc outside localChart guard accepted upstream scale
  exact index_soundness x n q qn zn D1 sc anchor ord num scalar

end Sun28.Ordinary
#print axioms Sun28.Ordinary.scalar_step_range
#print axioms Sun28.Ordinary.index_soundness
#print axioms Sun28.Ordinary.marked_certificate_sound
