import InfiniteGenerator

/-! From a filtration-preserving local logarithm to the ratio of formal
parameters of any two nonzero multiples of one rational point. -/
namespace Sun28.Scalar
variable {K L : Type*} [Field K] [DecidableEq K] [Field L] {b : K}

/-- The restriction of the filtered elliptic formal logarithm to the
global points inside a local formal kernel. -/
structure FilteredLogarithm (w : AddValuation K (WithTop ℤ)) (v : AddValuation L (WithTop ℤ))
    (b : K) where
  kernel : AddSubgroup (curve b).Point
  formal {Q : (curve b).Point} : 0<w (reciprocal Q) → parameter Q≠0 → Q ∈ kernel
  log : kernel →+ L
  level (Q : kernel) (r : ℕ) (hr : 0<r) :
    ((r:ℤ):WithTop ℤ) ≤ v (log Q) ↔ ((r:ℤ):WithTop ℤ) ≤ w (parameter Q.1)

/-- Membership in all positive integral layers determines every finite positive order. -/
theorem eq_of_positive_layers {x y : WithTop ℤ} {a : ℤ} (ha : 0 < a) (hy : y=(a:WithTop ℤ))
    (levels : ∀ r : ℕ, 0<r → (((r:ℤ):WithTop ℤ) ≤ x ↔ ((r:ℤ):WithTop ℤ) ≤ y)) : x=y := by
  subst y
  have nn : (a.toNat:ℤ)=a := Int.toNat_of_nonneg ha.le
  have hpos : 0<a.toNat := by omega
  have low := (levels a.toNat hpos).mpr (by rw [nn])
  rw [nn] at low
  have high : ¬ ((((a.toNat+1:ℕ):ℤ):WithTop ℤ) ≤ x) := by
    intro h
    have hh := WithTop.coe_le_coe.mp ((levels (a.toNat+1) (by omega)).mp h)
    omega
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact (high le_top).elim
  obtain ⟨i,hi⟩ := WithTop.ne_top_iff_exists.mp hx
  rw [←hi] at low high ⊢
  have l := WithTop.coe_le_coe.mp low
  have h : ¬((a.toNat+1:ℕ):ℤ) ≤ i := fun t => high (WithTop.coe_le_coe.mpr t)
  exact WithTop.coe_inj.mpr (by omega)

/-- In the local logarithm the identity n(mP)=m(nP) is a scalar equality,
even if P itself does not belong to the formal kernel. -/
theorem FilteredLogarithm.cross_mul {w : AddValuation K (WithTop ℤ)} {v : AddValuation L (WithTop ℤ)}
    (C : FilteredLogarithm w v b) (P : (curve b).Point) (m n : ℤ)
    (hm : m • P ∈ C.kernel) (hn : n • P ∈ C.kernel) :
    (n:L) * C.log ⟨m • P,hm⟩ = (m:L) * C.log ⟨n • P,hn⟩ := by
  have eq : n • (⟨m • P,hm⟩:C.kernel) = m • (⟨n • P,hn⟩:C.kernel) := by
    apply Subtype.ext
    change n • (m • P) = m • (n • P)
    rw [←mul_zsmul,←mul_zsmul,mul_comm n m]
  simpa only [map_zsmul, zsmul_eq_mul] using congrArg C.log eq

/-- The local formal comparison follows for every point from the elliptic
formal logarithm on every positive layer and the valuation of rational integers. -/
theorem formalComparison_of_filteredLogarithm [CharZero K] {p : ℕ}
    (w : AddValuation K (WithTop ℤ)) (v : AddValuation L (WithTop ℤ))
    (C : FilteredLogarithm w v b) (hb : 0≤w b)
    (integerOrder : ∀ n : ℤ, n≠0 → v (n:L)=((padicValInt p n:ℤ):WithTop ℤ))
    (P : (curve b).Point) : FormalComparison p w P := by
  intro m n hm hn fm fn zm zn
  have log_order (Q : (curve b).Point) (f : 0<w (reciprocal Q)) (z : parameter Q≠0) :
      ∃ d : ℤ, w (parameter Q)=(d:WithTop ℤ) ∧ v (C.log ⟨Q,C.formal f z⟩) = (d:WithTop ℤ) := by
    have rn : reciprocal Q≠0 := by
      cases Q with
      | zero => exact False.elim (z rfl)
      | some x y ns =>
        change (-x/y) ≠ 0 at z
        have nz : x≠0 := by rintro rfl; simp at z
        exact inv_ne_zero nz
    obtain ⟨a,ha⟩ := finite_order w rn
    have ap : 0<a := WithTop.coe_lt_coe.mp (ha ▸ f)
    cases Q with
    | zero => exact False.elim (z rfl)
    | some x y ns =>
      obtain ⟨d,hd,hpar,_⟩ := formal_parameter w hb ns ap ha
      refine ⟨d,hpar,?_⟩
      exact eq_of_positive_layers hd rfl (fun j hj => by
        simpa only [show parameter (.some x y ns) = -x/y by rfl,hpar] using
          (C.level ⟨.some x y ns,C.formal f z⟩ j hj))
  obtain ⟨a,ha,la⟩ := log_order (m • P) fm zm
  obtain ⟨d,hd,ld⟩ := log_order (n • P) fn zn
  have eq := congrArg v (C.cross_mul P m n (C.formal fm zm) (C.formal fn zn))
  simp only [v.map_mul, integerOrder m hm, integerOrder n hn, la, ld, ←WithTop.coe_add] at eq
  have equal : (padicValInt p n:ℤ)+a=(padicValInt p m:ℤ)+d := WithTop.coe_inj.mp eq
  rw [w.map_div,ha,hd]
  exact WithTop.coe_inj.mpr (by omega)

end Sun28.Scalar
#print axioms Sun28.Scalar.eq_of_positive_layers
#print axioms Sun28.Scalar.FilteredLogarithm.cross_mul
#print axioms Sun28.Scalar.formalComparison_of_filteredLogarithm
