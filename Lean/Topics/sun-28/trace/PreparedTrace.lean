import QuadraticAverage

/-! Local completeness of the normalized two-factor trace at the bad primes,
including the prime 2. -/
namespace Sun28.ScalarTrace
variable {K : Type*} [Field K]

/-- A prepared pair of scaled tests gives an inverse product congruent to one
to twice the preparation precision, including when a test vanishes. -/
theorem inverse_weight_congruent (v : AddValuation K (WithTop ℤ)) {r x y : K} {e : ℤ}
    (he : 0<e) (hr : (0:WithTop ℤ) ≤ v r)
    (hx : (e:WithTop ℤ) ≤ v (x/r)) (hy : (e:WithTop ℤ) ≤ v (y/r^48)) :
    ((2*e:ℤ):WithTop ℤ) ≤ v ((weight r x y)⁻¹-1) := by
  have hh {u : K} (hu : (e:WithTop ℤ) ≤ v u) :
      ((2*e:ℤ):WithTop ℤ) ≤ v (r*u^2) := by
    have tmp := add_le_add hr (add_le_add hu hu)
    simpa [AddValuation.map_mul,AddValuation.map_pow,two_nsmul,two_mul] using tmp
  let a := r*(x/r)^2
  let b := r*(y/r^48)^2
  have ha : ((2*e:ℤ):WithTop ℤ) ≤ v a := hh hx
  have hb : ((2*e:ℤ):WithTop ℤ) ≤ v b := hh hy
  have hP : (0:WithTop ℤ) < ((2*e:ℤ):WithTop ℤ) := WithTop.coe_lt_coe.mpr (by omega)
  have hab : ((2*e:ℤ):WithTop ℤ) ≤ v (a*b) := by
    rw [v.map_mul]
    simpa only [add_zero] using add_le_add ha ((hP.trans_le hb).le)
  let U := weight r x y
  have eq : U-1 = a+b+a*b := by
    dsimp [U,weight,factor,a,b]; ring
  have hU : ((2*e:ℤ):WithTop ℤ) ≤ v (U-1) := by
    rw [eq]
    exact v.map_le_add (v.map_le_add ha hb) hab
  have hval : v U = 0 := by
    have hh' : v (1:K) < v (U-1) := by rw [v.map_one]; exact hP.trans_le hU
    simpa using v.map_eq_of_lt_sub hh'
  have hn : U ≠ 0 := by
    apply (AddValuation.ne_top_iff v).mp
    rw [hval]; exact WithTop.coe_ne_top
  have hi : U⁻¹-1 = -(U-1)/U := by field_simp; ring
  change ((2*e:ℤ):WithTop ℤ) ≤ v (U⁻¹-1)
  rw [hi,v.map_div,v.map_neg,hval,sub_zero]; exact hU

variable {F : Type*} [Field F] [Algebra F K] [CharZero F] [Algebra.IsQuadraticExtension F K]

/-- The normalized trace is 1 modulo the preparation prime. For q=2 the
loss equals v(2), compensated by the two factors' square terms. -/
theorem prepared_scalarTheta (v : AddValuation K (WithTop ℤ)) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    {r : F} {x y : K} {e d : ℤ} (he : 0<e) (hd : d ≤ e) (htwo : v (2:K)=(d:WithTop ℤ))
    (hr : (0:WithTop ℤ) ≤ v (algebraMap F K r))
    (hx : (e:WithTop ℤ) ≤ v (x/algebraMap F K r))
    (hy : (e:WithTop ℤ) ≤ v (y/(algebraMap F K r)^48))
    (hx' : (e:WithTop ℤ) ≤ v (σ x/algebraMap F K r))
    (hy' : (e:WithTop ℤ) ≤ v (σ y/(algebraMap F K r)^48)) :
    (e:WithTop ℤ) ≤ v (algebraMap F K (scalarTheta r x y)-1) ∧
    v (algebraMap F K (scalarTheta r x y))=0 := by
  let U := weight (algebraMap F K r) x y
  let V := weight (algebraMap F K r) (σ x) (σ y)
  have hu := inverse_weight_congruent v he hr hx hy
  have hv := inverse_weight_congruent v he hr hx' hy'
  have hb : ((2*e:ℤ):WithTop ℤ) ≤ v ((U⁻¹-1)+(V⁻¹-1)) := v.map_le_add hu hv
  have two0 : (2:K) ≠ 0 := by
    apply (AddValuation.ne_top_iff v).mp
    rw [htwo]; exact WithTop.coe_ne_top
  have eq : average U V -1 = ((U⁻¹-1)+(V⁻¹-1))/2 := by
    unfold average; field_simp; ring
  have hvθ : (e:WithTop ℤ) ≤ v (algebraMap F K (scalarTheta r x y)-1) := by
    rw [scalarTheta_embeddings σ hσ]; change _ ≤ v (average U V-1)
    rw [eq,v.map_div,htwo]
    have addneg := add_le_add hb (le_refl (-((d:WithTop ℤ))))
    rw [sub_eq_add_neg]
    apply le_trans _ addneg
    exact WithTop.coe_le_coe.mpr (show e ≤ 2*e+(-d) by omega)
  refine ⟨hvθ,?_⟩
  have positive : v (1:K) < v (algebraMap F K (scalarTheta r x y)-1) := by
    rw [v.map_one]
    exact (WithTop.coe_lt_coe.mpr he).trans_le hvθ
  simpa using v.map_eq_of_lt_sub positive

end Sun28.ScalarTrace
#print axioms Sun28.ScalarTrace.inverse_weight_congruent
#print axioms Sun28.ScalarTrace.prepared_scalarTheta
