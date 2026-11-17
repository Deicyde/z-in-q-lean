import TYZRepresentative

/-! The doubled trace of the recursively defined TYZ point, in the actual elliptic group. -/
namespace ZInQBlueprint.TYZ.Specialization.TraceAction
noncomputable section
attribute [local instance] Classical.decEq
open WeierstrassCurve.Affine

local macro "sourceSome" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `TYZSpecialization `ZInQBlueprint.TYZ.Specialization.sourceAction_some))
local macro "cmSome" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `TYZCompositum `ZInQBlueprint.TYZ.Specialization.multiplyI_some))

/-- An absolute lift acts as an additive automorphism of the geometric elliptic group. -/
def liftAction (σ : Gal) : A ≃+ A where
  toFun := sourceAction σ
  invFun := sourceAction σ.symm
  map_add' := map_add _
  left_inv := by
    intro P
    cases P with
    | zero => simp only [show Point.zero = (0:A) from rfl, map_zero]
    | some x y h =>
      obtain ⟨h₁,e₁⟩ := sourceSome σ x y h
      obtain ⟨h₂,e₂⟩ := sourceSome σ.symm _ _ h₁
      rw [e₁,e₂]; erw [Point.some.injEq]; simp
  right_inv := by
    intro P
    cases P with
    | zero => simp only [show Point.zero = (0:A) from rfl, map_zero]
    | some x y h =>
      obtain ⟨h₁,e₁⟩ := sourceSome σ.symm x y h
      obtain ⟨h₂,e₂⟩ := sourceSome σ _ _ h₁
      rw [e₁,e₂]; erw [Point.some.injEq]; simp

/-- A lift preserving a subfield in both directions gives the automorphism on its points. -/
def fieldLift {F : SubfieldQ} (σ : Gal) (hf : ∀ x ∈ F, σ x ∈ F)
    (hi : ∀ x ∈ F, σ.symm x ∈ F) : pointsOver F ≃+ pointsOver F where
  toFun P := ⟨sourceAction σ P.val, sourceAction_mem σ hf P.property⟩
  invFun P := ⟨sourceAction σ.symm P.val, sourceAction_mem σ.symm hi P.property⟩
  left_inv P := Subtype.ext ((liftAction σ).left_inv P.val)
  right_inv P := Subtype.ext ((liftAction σ).right_inv P.val)
  map_add' P Q := Subtype.ext (map_add _ P.val Q.val)

/-- Complex multiplication is defined over ℚ(i). -/
theorem commute_i (σ : Gal) (hi : σ (Rank.sqrtMinus 1) = Rank.sqrtMinus 1) (P : A) :
    sourceAction σ (multiplyI P) = multiplyI (sourceAction σ P) := by
  cases P with
  | zero => simp only [show Point.zero = (0:A) from rfl, map_zero]
  | some x y h =>
    obtain ⟨h₁,e₁⟩ := cmSome x y h
    obtain ⟨h₂,e₂⟩ := sourceSome σ _ _ h₁
    obtain ⟨h₃,e₃⟩ := sourceSome σ x y h
    obtain ⟨h₄,e₄⟩ := cmSome _ _ h₃
    rw [e₁,e₂,e₃,e₄]; erw [Point.some.injEq]; simp [hi]

def unitHom (u : GaussianUnit) : A →+ A :=
  match u with
  | .one => AddMonoidHom.id A
  | .negOne => -(AddMonoidHom.id A)
  | .i => multiplyI
  | .negI => -multiplyI

theorem unitHom_apply (u : GaussianUnit) (P : A) : unitHom u P = u.act P := by cases u <;> rfl

theorem unitHom_cusp (u : GaussianUnit) : unitHom u twiceCusp = twiceCusp := by
  have hi : multiplyI twiceCusp = twiceCusp := by
    unfold twiceCusp
    obtain ⟨h,e⟩ := cmSome 0 0 (by norm_num [nonsingular_iff, equation_iff, genusCurve])
    rw [e]; erw [Point.some.injEq]; simp
  have hn : -twiceCusp = twiceCusp := by
    apply neg_eq_of_add_eq_zero_left
    exact (two_nsmul _).symm.trans twice_twiceCusp
  cases u with
  | one => rfl
  | negOne => exact hn
  | i => exact hi
  | negI => exact (congrArg Neg.neg hi).trans hn

theorem commute_unit (σ : Gal) (hi : σ (Rank.sqrtMinus 1) = Rank.sqrtMinus 1)
    (u : GaussianUnit) (P : A) : sourceAction σ (unitHom u P) = unitHom u (sourceAction σ P) := by
  cases u with
  | one => rfl
  | negOne => exact map_neg _ _
  | i => exact commute_i σ hi P
  | negI => exact (map_neg _ _).trans (congrArg Neg.neg (commute_i σ hi P))

/-- D(P) = 2(σP+P). -/
def doubledTrace (σ : Gal) : A →+ A :=
  (sourceAction σ + AddMonoidHom.id A) + (sourceAction σ + AddMonoidHom.id A)

theorem doubledTrace_apply (σ : Gal) (P : A) : doubledTrace σ P = (2:ℕ) • (sourceAction σ P + P) :=
  (two_nsmul _).symm

theorem doubledTrace_unit (σ : Gal) (hi : σ (Rank.sqrtMinus 1) = Rank.sqrtMinus 1)
    (u : GaussianUnit) (P : A) : doubledTrace σ (u.act P) = unitHom u (doubledTrace σ P) := by
  rw [←unitHom_apply, doubledTrace_apply, doubledTrace_apply, commute_unit σ hi, map_nsmul, map_add]

/-- The two geometric genus-trace formulas of Lemma 3.21 and its class-seven paragraph,
for divisors of the fixed input. The lift of the genus character is common to the divisors. -/
structure LocalTraceLaw (D : RecursionData) (σ : Gal) (N : ℕ) : Prop where
  fixesI : σ (Rank.sqrtMinus 1) = Rank.sqrtMinus 1
  cusps : ∃ U V : A, (2:ℕ) • U = 0 ∧ (2:ℕ) • V = twiceCusp ∧
    (∀ e, e ∣ N → e%8=5 → ∃ k : ℤ, sourceAction σ (D.trace e) + D.trace e =
      genusNumber e • U + k • twiceCusp) ∧
    (∀ e, e ∣ N → e%8=7 → sourceAction σ (D.trace e) + D.trace e = genusNumber e • V)

/-- The real half-period V represents 1/2. Subtracting its CM image represents
(1−i)/2. Since [i] fixes C, the latter cusp is killed by two. -/
theorem doubled_cusp_difference (V : A) (hV : (2:ℕ) • V = twiceCusp) :
    (2:ℕ) • (V - multiplyI V) = 0 := by
  have hI : multiplyI twiceCusp = twiceCusp := unitHom_cusp .i
  calc (2:ℕ) • (V - multiplyI V) = (2:ℕ) • V - (2:ℕ) • multiplyI V := nsmul_sub V (multiplyI V) 2
       _ = _ := by rw [←map_nsmul,hV,hI,sub_self]

/-- The two raw trace laws with their two cusps obtained from a single half-period. -/
theorem LocalTraceLaw.ofHalfPeriod {D : RecursionData} {σ : Gal} {N : ℕ}
    (hi : σ (Rank.sqrtMinus 1) = Rank.sqrtMinus 1) (V : A)
    (hV : (2:ℕ) • V = twiceCusp)
    (five : ∀ e, e ∣ N → e%8=5 → ∃ k : ℤ, sourceAction σ (D.trace e) + D.trace e =
      genusNumber e • (V - multiplyI V) + k • twiceCusp)
    (seven : ∀ e, e ∣ N → e%8=7 → sourceAction σ (D.trace e) + D.trace e = genusNumber e • V) :
    LocalTraceLaw D σ N := ⟨hi,V - multiplyI V,V,doubled_cusp_difference V hV,hV,five,seven⟩

def baseCoefficient (n : ℕ) : ℤ := if n%8=7 then (genusNumber n : ℤ) else 0

private theorem double_five {M : Type*} [AddCommGroup M] (U C : M) (g : ℕ) (k : ℤ)
    (hU : (2:ℕ) • U = 0) (hC : (2:ℕ) • C = 0) : (2:ℕ) • (g • U + k • C) = 0 := by
  rw [smul_add,smul_comm (2:ℕ) g,smul_comm (2:ℕ) k,hU,hC,smul_zero,smul_zero,add_zero]

theorem doubled_genus {D : RecursionData} {σ : Gal} {N n : ℕ} (H : LocalTraceLaw D σ N)
    (hn : n ∣ N) (hr : n%8=5 ∨ n%8=7) :
    doubledTrace σ (D.trace n) = baseCoefficient n • twiceCusp := by
  obtain ⟨U,V,hU,hV,h5,h7⟩ := H.cusps
  rcases hr with r|r
  · obtain ⟨k,h⟩ := h5 n hn r
    rw [doubledTrace_apply,h,double_five U twiceCusp (genusNumber n) k hU twice_twiceCusp]
    simp [baseCoefficient,r]
  · rw [doubledTrace_apply,h7 n hn r,smul_comm (2:ℕ) (genusNumber n),hV]
    simp [baseCoefficient,r]

theorem factor_lt {n t : ℕ} (ht : t ∈ recursionFactors n) : n/t < n := by
  obtain ⟨hd,h1,_⟩ := Finset.mem_filter.mp ht
  exact Nat.div_lt_self (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) h1

theorem cofactor_odd_class {n t : ℕ} (ht : t ∈ recursionFactors n) (hr : n%8=5 ∨ n%8=7) :
    (n/t)%8=5 ∨ (n/t)%8=7 := by
  obtain ⟨hd,_,_,hr'⟩ := Finset.mem_filter.mp ht
  rcases hr' with h|h|h
  · exact Or.inl h
  · have h2 : 2 ∣ n/t := Nat.dvd_of_mod_eq_zero (by omega)
    have := h2.trans (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1)
    omega
  · exact Or.inr h

/-- The coefficient of the rational point (0,0) in the doubled trace. -/
def traceCoefficient (L : ℕ → ℤ) (n : ℕ) : ℤ :=
  baseCoefficient n - ∑ t ∈ (recursionFactors n).attach, L t.val * traceCoefficient L (n/t.val)
termination_by n
decreasing_by exact factor_lt t.property

theorem traceCoefficient_eq (L : ℕ → ℤ) (n : ℕ) :
    traceCoefficient L n = baseCoefficient n - ∑ t ∈ recursionFactors n, L t * traceCoefficient L (n/t) := by
  rw [traceCoefficient, Finset.sum_attach (recursionFactors n) (fun t : ℕ => L t * traceCoefficient L (n/t))]

private theorem sum_zsmul' {M : Type*} [AddCommGroup M] (s : Finset ℕ) (f : ℕ → ℤ) (C : M) :
    (∑ t ∈ s, f t) • C = ∑ t ∈ s, f t • C := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert t s h ih => rw [Finset.sum_insert h,Finset.sum_insert h,add_zsmul,ih]

/-- The Gaussian units all fix (0,0), so the coefficient recurrence has only ordinary integers. -/
theorem doubled_representative {D : RecursionData} {σ : Gal} {N : ℕ} (H : LocalTraceLaw D σ N)
    (n : ℕ) (hn : n ∣ N) (hr : n%8=5 ∨ n%8=7) :
    doubledTrace σ (representative D n) = traceCoefficient D.L n • twiceCusp := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [representative_eq, map_sub, map_sum, doubled_genus H hn hr, traceCoefficient_eq]
    have distribute (a b : ℤ) (C : A) : (a-b) • C = a • C - b • C := sub_smul a b C
    rw [distribute, sum_zsmul']
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    have hdiv := (Nat.mem_divisors.mp (Finset.mem_filter.mp ht).1).1
    rw [map_zsmul, doubledTrace_unit σ H.fixesI, ih _ (factor_lt ht) ((Nat.div_dvd_of_dvd hdiv).trans hn)
      (cofactor_odd_class ht hr), map_zsmul,unitHom_cusp,mul_zsmul]

/-- A torsion representative defined over ℚ(i) and killed by four has vanishing doubled trace. -/
theorem vanishing_of_torsion {σ : Gal} (hi : σ (Rank.sqrtMinus 1) = Rank.sqrtMinus 1)
    {P : A} (hP : P ∈ pointsOver (Rank.imaginaryField 1)) (h4 : (4:ℕ) • P = 0) :
    doubledTrace σ P = 0 := by
  have he : sourceAction σ P = P := hP σ ((fixes_imaginaryField_iff 1 σ).mpr hi)
  rw [doubledTrace_apply,he,←two_nsmul,←mul_nsmul]
  exact h4

theorem odd_cusp (b : ℤ) (hb : Odd b) : b • twiceCusp = twiceCusp := by
  obtain ⟨k,hk⟩ := hb
  have hz : (2:ℤ) • twiceCusp = 0 := by rw [two_zsmul,←two_nsmul,twice_twiceCusp]
  rw [hk,add_zsmul,one_zsmul,mul_comm,mul_zsmul,hz]
  exact (congrArg (· + twiceCusp) (zsmul_zero k)).trans (zero_add _)

/-- The torsion information is needed only for this one recursive representative. -/
theorem infinite_of_odd {D : RecursionData} {σ : Gal} {n : ℕ} (H : LocalTraceLaw D σ n)
    (hr : n%8=5 ∨ n%8=7)
    (hT : ∀ m : ℕ, 0 < m → m • representative D n = 0 →
      representative D n ∈ pointsOver (Rank.imaginaryField 1) ∧ (4:ℕ) • representative D n = 0)
    (hb : Odd (traceCoefficient D.L n)) : Rank.InfiniteOrder (representative D n) := by
  intro m hm hz
  obtain ⟨hQ,h4⟩ := hT m hm hz
  have h := doubled_representative H n (dvd_refl n) hr
  rw [vanishing_of_torsion H.fixesI hQ h4, odd_cusp _ hb] at h
  exact twiceCusp_ne_zero h.symm

#print axioms liftAction
#print axioms fieldLift
#print axioms commute_i
#print axioms unitHom_cusp
#print axioms doubledTrace_unit
#print axioms doubled_cusp_difference
#print axioms LocalTraceLaw.ofHalfPeriod
#print axioms doubled_genus
#print axioms doubled_representative
#print axioms vanishing_of_torsion
#print axioms infinite_of_odd
end
end ZInQBlueprint.TYZ.Specialization.TraceAction
