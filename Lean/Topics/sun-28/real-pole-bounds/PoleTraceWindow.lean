import PoleProductWindow

/-! A finite real threshold for the literal reciprocal product and rational trace. -/
namespace Sun28.RealPoleBounds
open ZInQ Sun28.Ordinary Sun28.ScalarTrace Sun28.Forward Sun28.WitnessIndices
noncomputable section

def normalized (D : OrdinaryTest→K0) (u : ℚ) (i : OrdinaryTest) : K0 :=
  D i/(algebraMap ℚ K0 u)^(orderRequired i+1)

def productAt (r u : ℚ) (D : OrdinaryTest→K0) : K0 :=
  weightProduct (algebraMap ℚ K0 r) (normalized D u) orderRequired

def thetaAt (r u : ℚ) (D : OrdinaryTest→K0) : ℚ :=
  ordinaryTrace r (normalized D u) orderRequired

theorem map_productAt (σ : K0 →+* ℝ) (r u : ℚ) (D : OrdinaryTest→K0) :
    σ (productAt r u D) = weightProduct (r:ℝ) (fun i=>σ (D i)/(u:ℝ)^(orderRequired i+1)) orderRequired := by
  simp [productAt,normalized,weightProduct,factor,map_prod,map_add,map_mul,map_pow,map_div₀]

theorem real_thetaAt (r u : ℚ) (D : OrdinaryTest→K0) :
    (thetaAt r u D:ℝ) = (K0.embPlus (productAt r u D))⁻¹+
    ((K0.embPlus.comp conjugation.toRingHom) (productAt r u D))⁻¹ := by
  have e:=congrArg K0.embPlus (ordinaryTrace_eq conjugation conjugation_nontrivial r (normalized D u) orderRequired)
  simpa [thetaAt,productAt,normalized,weightProduct,factor,map_prod,map_add,map_mul,map_pow,map_div₀] using e

/-- Concrete lower trace bound and arbitrary epsilon, for any sixteen field-valued entries. -/
theorem detector_trace_small {A t : ℚ} {C ε : ℝ} (ap : 0<A) (ep : 0<ε)
    (late : depthThreshold A C ε < (t-3:ℚ)) (D : OrdinaryTest→K0)
    (bounded : ∀ i,∀ σ : K0 →+* ℝ, |σ (D i)|≤C) :
    t∉marks ∧ t≠3 ∧ 0<detector A t ∧ productAt (detector A t) (t-3) D≠0 ∧
    (2:ℝ)⁻¹^16 ≤ (thetaAt (detector A t) (t-3) D:ℝ) ∧ 0<thetaAt (detector A t) (t-3) D ∧
    0<detector A t/(thetaAt (detector A t) (t-3) D)^2 ∧
    ((detector A t/(thetaAt (detector A t) (t-3) D)^2:ℚ):ℝ) < ε := by
  let u : ℚ:=t-3
  let r:=detector A t
  let T:=thetaAt r u D
  have up4 : (4:ℝ)<u := (le_max_left _ _).trans_lt late
  have uq : (4:ℚ)<u := by exact_mod_cast up4
  have tl : 7<t := by dsimp [u] at uq;linarith
  have unmarked : t∉marks := by
    intro h
    norm_num [marks] at h
    rcases h with rfl|rfl|rfl|rfl|rfl <;> norm_num at tl
  obtain ⟨rp,low,hi⟩:=detector_window ap tl.le
  have r0 : (0:ℝ)<r := by exact_mod_cast rp
  have a0 : (0:ℝ)<A := by exact_mod_cast ap
  have u0 : (0:ℝ)<u:=by linarith
  have lower : 1/(A:ℝ)^5 ≤ (r:ℝ)*(u:ℝ) := by exact_mod_cast low
  have upper : (r:ℝ)*(u:ℝ) ≤ 32/(A:ℝ)^5 := by exact_mod_cast hi
  have depth : C*loss A < u := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt late)
  have limit : (32/(A:ℝ)^5)*(max 1 ((2:ℝ)^32/ε)) < u :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt late)
  have Mpos : 0≤32/(A:ℝ)^5 := by positivity
  have room : (32/(A:ℝ)^5)<u := by
    have := mul_le_mul_of_nonneg_left (le_max_left (1:ℝ) ((2:ℝ)^32/ε)) Mpos
    simpa only [mul_one] using this.trans_lt limit
  have rsmall : (r:ℝ)≤1 := by
    have z : (r:ℝ)*(u:ℝ)≤1*(u:ℝ) := (upper.trans room.le).trans_eq (one_mul _).symm
    exact (mul_le_mul_iff_left₀ u0).mp z
  have target : (r:ℝ)*2^32 < ε := by
    have b:=mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) ((2:ℝ)^32/ε)) Mpos
    have v : (32/(A:ℝ)^5)*2^32 < (u:ℝ)*ε := by
      apply (div_lt_iff₀ ep).mp
      simpa only [mul_div_assoc] using b.trans_lt limit
    have ru : (r:ℝ)*(u:ℝ)*2^32 < ε*(u:ℝ) :=
      (mul_le_mul_of_nonneg_right upper (by norm_num : (0:ℝ)≤2^32)).trans_lt (by linarith only [v])
    apply (mul_lt_mul_iff_left₀ u0).mp
    linarith only [ru]
  have prod (σ : K0 →+* ℝ) :
      1≤σ (productAt r u D) ∧ σ (productAt r u D)≤2^16 := by
    rw [map_productAt]
    exact bounded_product a0 u0 r0 rsmall lower depth.le _ (fun i=>bounded i σ)
  have nz : productAt r u D≠0 := by
    intro hz
    have h:=(prod K0.embPlus).1
    rw [hz,map_zero] at h
    norm_num at h
  have plus := prod K0.embPlus
  have minus := prod (K0.embPlus.comp conjugation.toRingHom)
  have pl : 0<K0.embPlus (productAt r u D):=zero_lt_one.trans_le plus.1
  have mi : 0<(K0.embPlus.comp conjugation.toRingHom) (productAt r u D):=zero_lt_one.trans_le minus.1
  have tlow : (2:ℝ)⁻¹^16 ≤ (T:ℝ) := by
    change _≤(thetaAt r u D:ℝ)
    rw [real_thetaAt]
    have inv := one_div_le_one_div_of_le pl plus.2
    have invm := inv_pos.mpr mi
    rw [one_div,one_div,←inv_pow] at inv
    linarith
  have tp : (0:ℝ)<T := (by norm_num : (0:ℝ)<2⁻¹^16).trans_le tlow
  have tq : (0:ℚ)<T := by exact_mod_cast tp
  have rlim : (r:ℝ)<ε*(2⁻¹^16)^2 := by norm_num at target ⊢;linarith
  have sq : (2⁻¹^16)^2≤(T:ℝ)^2 := pow_le_pow_left₀ (by norm_num) tlow 2
  have size : (r:ℝ)/(T:ℝ)^2<ε :=
    (div_lt_iff₀ (sq_pos_of_pos tp)).2 (rlim.trans_le (mul_le_mul_of_nonneg_left sq ep.le))
  exact ⟨unmarked,by linarith,rp,nz,tlow,tq,div_pos rp (sq_pos_of_pos tq),by exact_mod_cast size⟩

theorem bounded_ordinary_pole (w : NinePoints) (M : ℕ) (anchor : ℤ) (β A t : ℚ)
    (C ε : ℝ) (ap : 0<A) (ep : 0<ε) (late : depthThreshold A C ε < (t-3:ℚ))
    (bounded : ∀ i,∀ σ : K0 →+* ℝ,|σ (ordinaryAt w M anchor β i)|≤C) :
    t∉marks ∧ t≠3 ∧ 0<detector A t ∧ productAt (detector A t) (t-3) (ordinaryAt w M anchor β)≠0 ∧
    0<ordinaryTraceAt w M anchor β A t ∧
    0<detector A t/(ordinaryTraceAt w M anchor β A t)^2 ∧
    ((detector A t/(ordinaryTraceAt w M anchor β A t)^2:ℚ):ℝ)<ε := by
  obtain ⟨ns,ng,rp,nz,_,tp,bp,bε⟩:=detector_trace_small ap ep late _ bounded
  exact ⟨ns,ng,rp,nz,tp,bp,bε⟩

end
end Sun28.RealPoleBounds
#print axioms Sun28.RealPoleBounds.map_productAt
#print axioms Sun28.RealPoleBounds.real_thetaAt
#print axioms Sun28.RealPoleBounds.detector_trace_small
#print axioms Sun28.RealPoleBounds.bounded_ordinary_pole
