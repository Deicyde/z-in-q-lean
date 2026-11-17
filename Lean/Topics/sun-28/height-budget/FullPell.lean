import PrimeBudget

namespace Sun28.HeightBudget
open Sun28.FiveMarkUnits Sun28.HeightExtension Sun28.HeightFibres Sun28.HeightFibres.Sharp Height
noncomputable section
set_option maxRecDepth 8192
set_option exponentiation.threshold 650

/-- Bérczes–Evertse–Győry (3.8) and (3.14), restricted to rational S-integers
in a number field of degree at most four. All places above P are included. -/
def PublishedAllPell : Prop :=
  ∀ (L : IntermediateField ℚ Omega) [FiniteDimensional ℚ L], Module.finrank ℚ L≤4 →
    ∀ (P : Finset ℕ), (∀ p∈P,p.Prime) →
    ∃ a : PlacesData,
      a.primeNorm≤(primeProduct P:ℝ)^4 ∧ 0≤a.logarithmQ ∧ a.logarithmQ≤4*Real.log (primeProduct P:ℝ) ∧
      (P=∅ → a.regulator=NumberField.Units.regulator L) ∧
      a.regulator≤(NumberField.classNumber L:ℝ)*NumberField.Units.regulator L*(primeProduct P:ℝ)^2 ∧
      a.regulator≤(NumberField.classNumber L:ℝ)*NumberField.Units.regulator L*
        (max 1 (4*Real.log (primeProduct P:ℝ)))^(4*P.card) ∧
    ∀ (g h k I J : ℤ) (x y z : ℚ), g≠0 → h≠0 → k≠0 → I≠0 → J≠0 → I≠J →
      (∃ r:L,r^2=(g:L)/(h:L)) → (∃ w:L,w^2=(g:L)/(k:L)) →
      x.den.primeFactors⊆P → y.den.primeFactors⊆P → z.den.primeFactors⊆P →
      (g:ℚ)*x^2-(h:ℚ)*y^2=(I:ℚ) → (g:ℚ)*x^2-(k:ℚ)*z^2=(J:ℚ) →
      ∀ H B:ℝ, numberLog g≤H → numberLog h≤H → numberLog k≤H → numberLog I≤B → numberLog J≤B →
      logHeight₁ x ≤ (pellConstant (4*(P.card+1)):ℝ)*a.primeNorm*a.regulator*(1+logStar a.regulator)*
        (NumberField.Units.regulator L+(NumberField.classNumber L:ℝ)*a.logarithmQ+4*H+B)

theorem finite_of_all (pub : PublishedAllPell) : PublishedFinitePell := by
  intro L hf dim P pr budget
  obtain ⟨a,pa,qp,q,_,_,rs,main⟩:=pub L dim P pr
  refine ⟨a,pa,qp,q,rs.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (le_max_left ..) (by omega:4*P.card≤16)) (mul_nonneg (Nat.cast_nonneg _) (NumberField.Units.regulator_pos L).le)),?_⟩
  intro g h k I J x y z ng nh nk ni nj ij s₁ s₂ dx dy dz eq₁ eq₂ H B h₁ h₂ h₃ j₁ j₂
  apply (main g h k I J x y z ng nh nk ni nj ij s₁ s₂ dx dy dz eq₁ eq₂ H B h₁ h₂ h₃ j₁ j₂).trans
  have cap : pellConstant (4*(P.card+1))≤2^512 := by
    have test : ∀ r : Fin 5,pellConstant (4*(r.val+1))≤2^512:=by decide
    exact test ⟨P.card,by omega⟩
  have hr : 0≤1+logStar a.regulator:=by unfold logStar;linarith [le_max_left (1:ℝ) (Real.log a.regulator)]
  have last : 0≤NumberField.Units.regulator L+(NumberField.classNumber L:ℝ)*a.logarithmQ+4*H+B:=by
    have rg:0≤NumberField.Units.regulator L:=(NumberField.Units.regulator_pos L).le
    have hH:0≤H:=(nonneg_numberLog ng).trans h₁
    have hB:0≤B:=(nonneg_numberLog ni).trans j₁
    positivity
  have cr : (pellConstant (4*(P.card+1)):ℝ)≤2^512:=by exact_mod_cast cap
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right cr (zero_le_one.trans a.one_le_primeNorm)) a.regulator_pos.le) hr) last

theorem integral_of_all (pub : PublishedAllPell) : PublishedPell312 := by
  intro L hf dim g h k a b c I J ng nh nk ni nj ij s₁ s₂ e₁ e₂ H B h₁ h₂ h₃ j₁ j₂
  obtain ⟨p,norm,qp,q,reg,_,_,main⟩:=pub L dim ∅ (by simp)
  have u : p.primeNorm=1:=le_antisymm (by simpa [primeProduct] using norm) p.one_le_primeNorm
  have v : p.logarithmQ=0:=le_antisymm (by simpa [primeProduct] using q) qp
  have Q₁ : (g:ℚ)*(a:ℚ)^2-(h:ℚ)*(b:ℚ)^2=I:=by exact_mod_cast e₁
  have Q₂ : (g:ℚ)*(a:ℚ)^2-(k:ℚ)*(c:ℚ)^2=J:=by exact_mod_cast e₂
  have out:=main g h k I J a b c ng nh nk ni nj ij s₁ s₂ (by simp) (by simp) (by simp) Q₁ Q₂
    H B h₁ h₂ h₃ j₁ j₂
  have le : numberLog a≤logHeight₁ (a:ℚ):=by
    rw [Rat.logHeight₁_eq_log_max]
    change Real.log (a.natAbs:ℝ)≤ Real.log ((max a.natAbs 1:ℕ):ℝ)
    by_cases z:a=0
    · subst a;norm_num
    · exact Real.log_le_log (by exact_mod_cast Int.natAbs_pos.mpr z) (by exact_mod_cast le_max_left a.natAbs 1)
  have cc : pellConstant 4=2^140:=by decide
  simpa only [Finset.card_empty,zero_add,mul_one,cc,Nat.cast_pow,Nat.cast_ofNat,u,v,reg rfl,mul_zero,add_zero]
    using le.trans out

end
end Sun28.HeightBudget
#print axioms Sun28.HeightBudget.finite_of_all
#print axioms Sun28.HeightBudget.integral_of_all
