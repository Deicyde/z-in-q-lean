import Mathlib

/-! Conjugation of the Picard sextic on its invertible-coordinate chart. All
twists use the same number field and the same change of coordinates. -/

namespace ZOverQ.Qualitative.PicardConjugation

noncomputable section

def binarySextic {A : Type*} [CommRing A] (u v x z : A) : A :=
  (x^2 + 2*x*z - 2*z^2) * (4*u*(2*x-z)*z^3 - v*x^3*(x+4*z))

theorem binary_swap {A : Type*} [CommRing A] (u v x z : A) :
    binarySextic u v (-2*z) x = -8 * binarySextic v u x z := by
  unfold binarySextic
  ring

theorem binary_scale {A : Type*} [CommRing A] (u v x z a : A) :
    binarySextic u v (a*x) (a*z) = a^6 * binarySextic u v x z := by
  unfold binarySextic
  ring

variable {K : Type*} [Field K] [CharZero K]

/-- The two coordinates on the finite affine curve away from x = 0. -/
def AffinePoint (u v d : K) :=
  {p : K × K // p.1 ≠ 0 ∧ 2*d*p.2^2 = binarySextic u v p.1 1}

theorem affine_swap (u v x : K) (hx : x ≠ 0) :
    x^6 * binarySextic u v (-2/x) 1 = -8 * binarySextic v u x 1 := by
  have h := binary_scale u v (-2/x) 1 x
  rw [mul_one, show x * (-2/x) = -2 from by field_simp] at h
  simpa only [mul_one] using h.symm.trans (by simpa only [mul_one] using binary_swap u v x 1)

def affineMove (u v d r : K) (hr : r^2 = -2) (p : AffinePoint v u d) :
    AffinePoint u v d := by
  rcases p with ⟨⟨x,y⟩,hx,hy⟩
  refine ⟨(-2/x, 2*r*y/x^3), div_ne_zero (by norm_num) hx, ?_⟩
  change 2*d*(2*r*y/x^3)^2 = _
  apply mul_left_cancel₀ (pow_ne_zero 6 hx)
  rw [affine_swap _ _ _ hx]
  calc
    x^6 * (2*d*(2*r*y/x^3)^2) = (4*r^2)*(2*d*y^2) := by field_simp; ring
    _ = -8 * binarySextic v u x 1 := by rw [hr, hy]; ring

private theorem affineMove_twice (u v d r : K) (hr : r^2 = -2) (p : AffinePoint u v d) :
    affineMove u v d r hr (affineMove v u d r hr p) = p := by
  rcases p with ⟨⟨x,y⟩,hx,hy⟩
  apply Subtype.ext
  apply Prod.ext
  · change -2 / (-2 / x) = x
    field_simp
  · change 2*r*(2*r*y/x^3)/(-2/x)^3 = y
    calc
      _ = -r^2*y/2 := by field_simp
      _ = y := by rw [hr]; ring

/-- Both directions are given by (x,y) ↦ (−2/x,2r y/x³), where r² = −2. -/
def affineEquiv (u v d r : K) (hr : r^2 = -2) : AffinePoint v u d ≃ AffinePoint u v d where
  toFun := affineMove u v d r hr
  invFun := affineMove v u d r hr
  left_inv := affineMove_twice v u d r hr
  right_inv := affineMove_twice u v d r hr

/-- On the opposite full charts the change of coordinates is linear, including x=0. -/
def finiteReciprocalEquiv (u v d r : K) (hr : r^2 = -2) :
    {p : K × K // 2*d*p.2^2 = binarySextic v u p.1 1} ≃
      {p : K × K // 2*d*p.2^2 = binarySextic u v 1 p.1} where
  toFun := fun ⟨⟨x,y⟩,hy⟩ => ⟨(-x/2,-r*y/4), by
    change 2*d*(-r*y/4)^2 = binarySextic u v 1 (-x/2)
    have h : binarySextic u v 1 (-x/2) = (-1/8)*binarySextic v u x 1 := by
      unfold binarySextic
      ring
    rw [h]
    change 2*d*y^2 = binarySextic v u x 1 at hy
    linear_combination (d*y^2/8)*hr - (1/8)*hy⟩
  invFun := fun ⟨⟨z,w⟩,hw⟩ => ⟨(-2*z,2*r*w), by
    change 2*d*(2*r*w)^2 = binarySextic v u (-2*z) 1
    rw [binary_swap]
    change 2*d*w^2 = binarySextic u v 1 z at hw
    linear_combination 8*d*w^2*hr - 8*hw⟩
  left_inv := by
    rintro ⟨⟨x,y⟩,_⟩
    apply Subtype.ext
    apply Prod.ext
    · change -2*(-x/2)=x
      ring
    · change 2*r*(-r*y/4)=y
      linear_combination -(y/2)*hr
  right_inv := by
    rintro ⟨⟨z,w⟩,_⟩
    apply Subtype.ext
    apply Prod.ext
    · change -(-2*z)/2=z
      ring
    · change -r*(2*r*w)/4=w
      linear_combination -(w/2)*hr

/-- In the reciprocal chart the point x=0 maps to z'=0, w'=−r y/4. -/
def boundaryEquiv (u v d r : K) (hr : r^2 = -2) :
    {y : K // 2*d*y^2 = binarySextic v u 0 1} ≃
      {w : K // 2*d*w^2 = binarySextic u v 1 0} where
  toFun := fun ⟨y,hy⟩ => ⟨-r*y/4, by
    have h : 2*d*y^2 = 8*v := by
      rw [hy]
      unfold binarySextic
      ring
    simp only [binarySextic]
    linear_combination (d*y^2/8)*hr - (1/8)*h⟩
  invFun := fun ⟨w,hw⟩ => ⟨2*r*w, by
    have h : 2*d*w^2 = -v := by simpa [binarySextic] using hw
    simp only [binarySextic]
    linear_combination 8*d*w^2*hr - 8*h⟩
  left_inv := by
    rintro ⟨y,_⟩
    apply Subtype.ext
    change 2*r*(-r*y/4) = y
    linear_combination -(y/2)*hr
  right_inv := by
    rintro ⟨w,_⟩
    apply Subtype.ext
    change -r*(2*r*w)/4 = w
    linear_combination -(w/2)*hr

theorem finite_boundary (d a : K) (hd : d ≠ 0) :
    Set.Finite {y : K | 2*d*y^2 = a} := by
  by_cases h : ∃ y : K, 2*d*y^2 = a
  · obtain ⟨z,hz⟩ := h
    apply ((Set.finite_singleton (-z)).insert z).subset
    intro y hy
    have e : y^2 = z^2 := mul_left_cancel₀ (mul_ne_zero (by norm_num) hd) (hy.trans hz.symm)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with e | e <;> simp [e]
  · apply Set.finite_empty.subset
    intro y hy
    exact False.elim (h ⟨y,hy⟩)

/-! The localized chart ring is presented by adjoining the inverse of x. -/
open MvPolynomial

def OnChart {A : Type*} [CommRing A] (u v d : A) (p : Fin 3 → A) : Prop :=
  p 0 * p 1 = 1 ∧ 2*d*(p 2)^2 = binarySextic u v (p 0) 1

private def transformed {A : Type*} [CommRing A] (c k : A) (p : Fin 3 → A) : Fin 3 → A :=
  ![-2*p 1, c*p 0, k*p 2*(p 1)^3]

private theorem transformed_onChart {A : Type*} [CommRing A] {u v d c k : A}
    (hc : -2*c = 1) (hk : k^2 = -8) {p : Fin 3 → A} (hp : OnChart v u d p) :
    OnChart u v d (transformed c k p) := by
  obtain ⟨hx,hy⟩ := hp
  constructor
  · change (-2*p 1)*(c*p 0) = 1
    calc
      _ = (-2*c)*(p 0*p 1) := by ring
      _ = 1 := by rw [hc,hx,mul_one]
  · change 2*d*(k*p 2*(p 1)^3)^2 = binarySextic u v (-2*p 1) 1
    have scale := binary_scale v u (p 0) 1 (p 1)
    rw [mul_one, mul_comm (p 1) (p 0), hx] at scale
    calc
      _ = k^2 * ((p 1)^6 * (2*d*(p 2)^2)) := by ring
      _ = -8 * binarySextic v u 1 (p 1) := by rw [hk,hy,← scale]
      _ = binarySextic u v (-2*p 1) 1 := (binary_swap u v 1 (p 1)).symm

private theorem transformed_twice {A : Type*} [CommRing A] {c k : A}
    (hc : -2*c = 1) (hk : k^2 = -8) {p : Fin 3 → A} (hx : p 0*p 1=1) :
    transformed c k (transformed c k p) = p := by
  funext i
  fin_cases i
  · change -2*(c*p 0) = p 0
    rw [← mul_assoc,hc,one_mul]
  · change c*(-2*p 1) = p 1
    rw [← mul_assoc,mul_comm c,hc,one_mul]
  · change k*(k*p 2*(p 1)^3)*(c*p 0)^3 = p 2
    have hunit : (-8:A)*c^3 = 1 := by
      calc
        _ = (-2*c)^3 := by ring
        _ = 1 := by rw [hc,one_pow]
    calc
      _ = (k^2*c^3)*(p 0*p 1)^3*p 2 := by ring
      _ = p 2 := by rw [hk,hunit,hx,one_pow,one_mul,one_mul]

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

private def cScalar (K A : Type*) [Field K] [CommRing A] [Algebra K A] : A :=
  algebraMap K A (-1/2)

private def kScalar (A : Type*) [CommRing A] [Algebra K A] (r : K) : A :=
  algebraMap K A (2*r)

private theorem cScalar_rel : -2*cScalar K A = 1 := by
  have h := congrArg (algebraMap K A) (show (-2:K)*(-1/2)=1 by norm_num)
  simpa only [map_mul,map_neg,map_ofNat,map_one,cScalar] using h

omit [CharZero K] in
private theorem kScalar_rel {r : K} (hr : r^2 = -2) : kScalar A r ^ 2 = -8 := by
  have h : (2*r)^2 = -8 := by rw [mul_pow,hr]; norm_num
  simpa only [kScalar,map_pow,map_neg,map_ofNat] using congrArg (algebraMap K A) h

private def invRel : MvPolynomial (Fin 3) K := X 0 * X 1 - 1

private def curveRel (u v d : K) : MvPolynomial (Fin 3) K :=
  2*C d*(X 2)^2 - binarySextic (C u) (C v) (X 0) 1

private def chartIdeal (u v d : K) : Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span {invRel, curveRel u v d}

/-- K[x,z,y]/(xz−1, 2d y²−f(u,v,x)), the finite sextic chart localized at x. -/
abbrev ChartRing (u v d : K) := MvPolynomial (Fin 3) K ⧸ chartIdeal u v d

def coord (u v d : K) (i : Fin 3) : ChartRing u v d := Ideal.Quotient.mk _ (X i)

omit [CharZero K] in
private theorem eval_invRel (p : Fin 3 → A) :
    aeval p (invRel (K:=K)) = p 0*p 1-1 := by simp [invRel]

omit [CharZero K] in
private theorem eval_curveRel (u v d : K) (p : Fin 3 → A) :
    aeval p (curveRel u v d) = 2*(algebraMap K A d)*(p 2)^2 -
      binarySextic (algebraMap K A u) (algebraMap K A v) (p 0) 1 := by
  simp [curveRel,binarySextic]

omit [CharZero K] in
private theorem coord_onChart (u v d : K) :
    OnChart (algebraMap K _ u) (algebraMap K _ v) (algebraMap K _ d) (coord u v d) := by
  have ev : aeval (coord u v d) = Ideal.Quotient.mkₐ K (chartIdeal u v d) := by
    apply MvPolynomial.algHom_ext
    intro i
    exact aeval_X _ _
  have hz (p : MvPolynomial (Fin 3) K) (h : p ∈ chartIdeal u v d) :
      aeval (coord u v d) p = 0 := by
    rw [ev]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h
  constructor
  · apply sub_eq_zero.mp
    rw [← eval_invRel (K:=K)]
    exact hz _ (Ideal.subset_span (by simp))
  · apply sub_eq_zero.mp
    rw [← eval_curveRel]
    exact hz _ (Ideal.subset_span (by simp))

private def evaluate (u v d : K) (p : Fin 3 → A)
    (hp : OnChart (algebraMap K A u) (algebraMap K A v) (algebraMap K A d) p) :
    ChartRing u v d →ₐ[K] A :=
  Ideal.Quotient.liftₐ _ (aeval p) fun _ hf => by
    have h : chartIdeal u v d ≤ RingHom.ker (aeval p : _ →ₐ[K] A) := by
      apply Ideal.span_le.mpr
      intro f hf
      rcases Set.mem_insert_iff.mp hf with h | h
      · subst f
        change aeval p invRel = 0
        rw [eval_invRel, hp.1, sub_self]
      · rw [Set.mem_singleton_iff.mp h]
        change aeval p (curveRel u v d) = 0
        rw [eval_curveRel, hp.2, sub_self]
    exact h hf

omit [CharZero K] in
private theorem evaluate_coord (u v d : K) (p : Fin 3 → A) (hp) (i : Fin 3) :
    evaluate u v d p hp (coord u v d i) = p i :=
  (Ideal.Quotient.liftₐ_apply _ _ _ _).trans (aeval_X _ _)

private def conjugationHom (u v d r : K) (hr : r^2 = -2) :
    ChartRing u v d →ₐ[K] ChartRing v u d :=
  evaluate u v d (transformed (cScalar K _) (kScalar _ r) (coord v u d))
    (transformed_onChart cScalar_rel (kScalar_rel hr) (coord_onChart v u d))

omit [CharZero K] in
private theorem map_transformed (φ : A →ₐ[K] B) (r : K) (p : Fin 3 → A) (i : Fin 3) :
    φ (transformed (cScalar K A) (kScalar A r) p i) =
      transformed (cScalar K B) (kScalar B r) (φ ∘ p) i := by
  fin_cases i <;> simp [transformed,cScalar,kScalar,map_ofNat]

private theorem conjugationHom_comp (u v d r : K) (hr : r^2 = -2) :
    (conjugationHom v u d r hr).comp (conjugationHom u v d r hr) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change conjugationHom v u d r hr (conjugationHom u v d r hr (coord u v d i)) = coord u v d i
  have h (a b : K) (j : Fin 3) : conjugationHom a b d r hr (coord a b d j) =
      transformed (cScalar K _) (kScalar _ r) (coord b a d) j := evaluate_coord ..
  rw [h,map_transformed]
  have he : conjugationHom v u d r hr ∘ coord v u d =
      transformed (cScalar K _) (kScalar _ r) (coord u v d) := funext (h v u)
  rw [he, transformed_twice cScalar_rel (kScalar_rel hr) (coord_onChart u v d).1]

/-- The isomorphism of localized coordinate rings, contravariant in the affine curves. -/
def chartAlgEquiv (u v d r : K) (hr : r^2 = -2) :
    ChartRing u v d ≃ₐ[K] ChartRing v u d :=
  AlgEquiv.ofAlgHom (conjugationHom u v d r hr) (conjugationHom v u d r hr)
    (conjugationHom_comp v u d r hr) (conjugationHom_comp u v d r hr)

/-- The induced equivalence of total rings of fractions. For integral charts these are fields. -/
def chartFractionEquiv (u v d r : K) (hr : r^2 = -2) :
    FractionRing (ChartRing u v d) ≃ₐ[K] FractionRing (ChartRing v u d) :=
  IsFractionRing.algEquivOfAlgEquiv (chartAlgEquiv u v d r hr)

abbrev Qbar := AlgebraicClosure ℚ

private def radical (n : ℕ) : Qbar :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (-(n : Qbar)) zero_lt_two)

private theorem radical_sq (n : ℕ) : radical n ^ 2 = -(n : Qbar) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (-(n : Qbar)) zero_lt_two)

/-- The single number field Q(√−2,√−3) for the whole family. -/
def fixedField : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {radical 2, radical 3}

instance : NumberField fixedField where
  to_charZero := inferInstance
  to_finiteDimensional := IntermediateField.finiteDimensional_adjoin_pair
    (Algebra.IsIntegral.isIntegral (radical 2)) (Algebra.IsIntegral.isIntegral (radical 3))

def r : fixedField := ⟨radical 2, IntermediateField.mem_adjoin_pair_left ℚ (radical 2) (radical 3)⟩
def ρ : fixedField := ⟨radical 3, IntermediateField.mem_adjoin_pair_right ℚ (radical 2) (radical 3)⟩

theorem r_sq : r^2 = -2 := by
  apply Subtype.ext
  change (radical 2)^2 = -(2:Qbar)
  simpa only [Nat.cast_ofNat] using radical_sq 2

theorem rho_sq : ρ^2 = -3 := by
  apply Subtype.ext
  change (radical 3)^2 = -(3:Qbar)
  simpa only [Nat.cast_ofNat] using radical_sq 3

instance : IsGalois ℚ fixedField where
  to_normal := by
    apply IntermediateField.normal_iff_forall_map_le.mpr
    intro σ
    rw [show fixedField = IntermediateField.adjoin ℚ {radical 2,radical 3} from rfl,
      IntermediateField.adjoin_map]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨x,hx,rfl⟩
    have root (n : ℕ) (h : radical n ∈ fixedField) : σ (radical n) ∈ fixedField := by
      have e : (σ (radical n))^2 = (radical n)^2 := by
        rw [← map_pow,radical_sq,map_neg,map_natCast]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with e | e
      · simpa only [e] using h
      · rw [e]
        exact neg_mem h
    rcases Set.mem_insert_iff.mp hx with h | h
    · rw [h]
      exact root 2 r.property
    · rw [Set.mem_singleton_iff.mp h]
      exact root 3 ρ.property

def U (s : ℚ) : fixedField := ((s:fixedField)+ρ)^6
def V (s : ℚ) : fixedField := ((s:fixedField)-ρ)^6

/-- A rational-field automorphism of the coefficient field carries the pair to
itself or swaps it; both cases are independent of the rational twist. -/
theorem coefficient_action (σ : fixedField ≃ₐ[ℚ] fixedField) (s : ℚ) :
    (σ (U s) = U s ∧ σ (V s) = V s) ∨ (σ (U s) = V s ∧ σ (V s) = U s) := by
  have h : (σ ρ)^2 = ρ^2 := by rw [← map_pow,rho_sq,map_neg,map_ofNat]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with e | e
  · left
    simp [U,V,e]
  · right
    simp [U,V,e,sub_eq_add_neg]

/-- Every Galois conjugate of every rationally twisted open chart has
isomorphic coordinate algebra over the same fixed number field. -/
theorem conjugate_chart (σ : fixedField ≃ₐ[ℚ] fixedField) (s d : ℚ) :
    Nonempty (ChartRing (U s) (V s) (d:fixedField) ≃ₐ[fixedField]
      ChartRing (σ (U s)) (σ (V s)) (σ (d:fixedField))) := by
  rw [map_ratCast]
  rcases coefficient_action σ s with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · rw [hu,hv]
    exact ⟨AlgEquiv.refl⟩
  · rw [hu,hv]
    exact ⟨chartAlgEquiv _ _ _ r r_sq⟩

end
end ZOverQ.Qualitative.PicardConjugation

#print axioms ZOverQ.Qualitative.PicardConjugation.affineEquiv
#print axioms ZOverQ.Qualitative.PicardConjugation.chartAlgEquiv
#print axioms ZOverQ.Qualitative.PicardConjugation.chartFractionEquiv
#print axioms ZOverQ.Qualitative.PicardConjugation.finiteReciprocalEquiv
#print axioms ZOverQ.Qualitative.PicardConjugation.boundaryEquiv
#print axioms ZOverQ.Qualitative.PicardConjugation.finite_boundary
#print axioms ZOverQ.Qualitative.PicardConjugation.conjugate_chart
