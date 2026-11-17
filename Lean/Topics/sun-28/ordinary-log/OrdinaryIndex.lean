import ClearedRatio

/-! The two ordinary rational tests at the point printed in Sun's paper. -/
namespace Sun28.Ordinary
open Sun28.Scalar Sun28.ScalarTrace NumberField IsDedekindDomain Filter Topology
open scoped NumberField BigOperators

private theorem natural_integral {L : Type*} [Field L] (v : AddValuation L (WithTop ℤ)) (n : ℕ) :
    0≤v (n:L) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ]; exact v.map_le_add ih (by simp)

/-- Coefficient of Z^{n-1} in (1-4bZ^4)^(-1/2), normalized at 1. -/
def shortDifferential {L : Type*} [Field L] (b : L) (n : ℕ) : L :=
  if n%4=1 then (Nat.choose (2*(n/4)) (n/4):L)*b^(n/4) else 0

theorem shortDifferential_integral {L : Type*} [Field L] (v : AddValuation L (WithTop ℤ))
    {b : L} (hb : 0≤v b) (n : ℕ) : 0≤v (shortDifferential b n) := by
  unfold shortDifferential
  split_ifs
  · rw [v.map_mul,v.map_pow]
    exact add_nonneg (natural_integral v _) (nsmul_nonneg hb _)
  · simp

theorem map_shortTrunc {K L : Type*} [Field K] [Field L] (f : K →+* L) (b z : K) (k : ℕ) :
    f (logTrunc (shortDifferential b) k z)=logTrunc (shortDifferential (f b)) k (f z) := by
  simp [logTrunc,shortDifferential,map_sum,apply_ite]

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

/-- A formal parameter chart and the convergence of the integral of its invariant
differential to an additive homomorphism. No truncation estimate or isometry enters. -/
def OrdinaryLogarithms (p : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop := by
  classical
  let L:=w.adicCompletion K
  let v:=completionOrder w
  exact ∀ b : L, 65<p → v (p:L)=1 → 0≤v b → v (curve b).Δ=0 →
    ∃ T : EllipticKernelChart v b, ∃ A : T.F →+ L,
      ∀ X : T.F, Tendsto (fun n => logTrunc (shortDifferential b) n (T.coordinate X)) atTop (𝓝 (A X))

/-- The common global index ratio, before embedding or conjugating it. -/
noncomputable def ordinaryRatio {b : K} (P : (curve b).Point) (m h : ℤ) : K :=
  logTrunc (shortDifferential b) 64 (parameter (m • P)) /
  logTrunc (shortDifferential b) 64 (parameter (h • P))

omit [Algebra.IsQuadraticExtension ℚ K] [DecidableEq K] in
private theorem integer_order {p : ℕ} [Fact p.Prime] (w : HeightOneSpectrum (𝓞 K))
    {v : HeightOneSpectrum (𝓞 ℚ)} [w.asIdeal.LiesOver v.asIdeal]
    (name : (Rat.HeightOneSpectrum.primesEquiv v).1=p) (unram : w.asIdeal.ramificationIdx (𝓞 ℚ)=1)
    (n : ℤ) (nz : n≠0) : completionOrder w (n:w.adicCompletion K)=((padicValInt p n:ℤ):WithTop ℤ) := by
  have eq := prime_order_rat v w (q:=(n:ℚ)) (by exact_mod_cast nz)
  rw [unram,name] at eq
  rw [←map_intCast (algebraMap K (w.adicCompletion K)),completionOrder_algebraMap]
  simpa [padicValRat.of_int] using eq

omit [Algebra.IsQuadraticExtension ℚ K] in
/-- The denominator and numerator on a nonzero cyclic point are formal as soon
as its reciprocal abscissa has positive order. -/
private theorem actual_depth (u : AddValuation K (WithTop ℤ)) {ρ : K} (root : ρ^2=2)
    (hb : 0≤u (-(3-ρ)^2)) {j : ℤ} (nonzero : j≠0)
    (high : (1:WithTop ℤ)≤u (reciprocal (j • paperGenerator root))) :
    parameter (j • paperGenerator root)≠0 ∧
      ∃ d : ℤ, 0<d ∧ u (parameter (j • paperGenerator root))=(d:WithTop ℤ) := by
  have hj (i : ℤ) (ni : i≠0) : i • paperGenerator root≠0 := by
    intro zero
    have h := addOrderOf_dvd_iff_zsmul_eq_zero.mpr zero
    rw [paperGenerator_infinite root] at h
    exact ni (by simpa using h)
  obtain ⟨recip,par⟩ := cyclic_middle_nonzero _ hj nonzero
  obtain ⟨a,ha⟩ := finite_order u recip
  have ap : 0<a := WithTop.coe_lt_coe.mp ((lt_of_lt_of_le (by decide : (0:WithTop ℤ)<1) high).trans_eq ha)
  refine ⟨par,?_⟩
  generalize heq : j • paperGenerator root = Q at recip par ha ⊢
  cases Q with
  | zero => exact False.elim (par rfl)
  | some x y on =>
    obtain ⟨d,hd,hz,_⟩ := formal_parameter u hb on ap ha
    exact ⟨d,hd,hz⟩

omit [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K] in
/-- Finite truncations determine the order of the full logarithm without a separate
isometry assumption. Use k=1, whose truncation equals the formal parameter. -/
private theorem series_order (w : HeightOneSpectrum (𝓞 K)) {p : ℕ} [Fact p.Prime]
    (large : 65<p) {b z S : w.adicCompletion K} (hb : 0≤completionOrder w b)
    (integerOrder : ∀ n : ℕ, n≠0 → completionOrder w (n:w.adicCompletion K)=((padicValNat p n:ℤ):WithTop ℤ))
    {d : ℤ} (hd : 0<d) (hz : completionOrder w z=(d:WithTop ℤ))
    (converges : Tendsto (fun n => logTrunc (shortDifferential b) n z) atTop (𝓝 S)) :
    completionOrder w S=(d:WithTop ℤ) := by
  have h := log_trunc_error w (k:=1) (p:=p) (by omega) _ (shortDifferential_integral _ hb) integerOrder hd hz converges
  have one : logTrunc (shortDifferential b) 1 z=z := by simp [logTrunc,shortDifferential]
  rw [one] at h
  have eq : completionOrder w (z-S)=completionOrder w (S-z) := (completionOrder w).map_sub_swap z S
  exact trunc_order _ hz (k:=1) (by decide) (eq.symm ▸ h)

/-- A degree-64 ratio gives the denominator-cleared integer congruence even
when the bare integer ratio has negative valuation. Conjugating the entire
global ratio transports every coefficient and point coordinate together. -/
theorem ordinary_index_ratio64 {p : ℕ} [Fact p.Prime] (large : 65<p)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (classicalInput : OrdinaryLogarithms p w) (τ : K ≃ₐ[ℚ] K)
    (m h : ℤ) (denom : h≠0)
    (fm : (1:WithTop ℤ)≤discreteOrder (w.valuation K) (τ (reciprocal (m • paperGenerator root))))
    (fh : (1:WithTop ℤ)≤discreteOrder (w.valuation K) (τ (reciprocal (h • paperGenerator root)))) :
    let u := discreteOrder (w.valuation K)
    let L := τ (ordinaryRatio (paperGenerator root) m h)
    u L=u ((m:K)/h) ∧ (64:WithTop ℤ)≤u ((h:K)*L-m) := by
  classical
  let L:=w.adicCompletion K
  let v:=completionOrder w
  let b : K := -(3-ρ)^2
  let P := paperGenerator root
  let u:=(discreteOrder (w.valuation K)).comap τ.toRingHom
  let f:K →+* L := (algebraMap K L).comp τ.toRingHom
  have agrees (x:K) : v (f x)=u x := completionOrder_algebraMap w (τ x)
  let vq := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv vq).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,Fact.out⟩)
  have unr := sqrtTwo_unramified root vq w name (by omega : 2<p)
  have intOrd (n : ℤ) (hn:n≠0) := integer_order w name unr n hn
  have natOrd (n:ℕ) (hn:n≠0) : v (n:L)=((padicValNat p n:ℤ):WithTop ℤ) := by
    simpa [padicValInt] using intOrd (n:ℤ) (by exact_mod_cast hn)
  obtain ⟨up,bi,du⟩ := good_scalar_prime (by omega : 2<p) (by omega : p≠7) w τ root
  have localint : 0≤v (f b) := (agrees b).symm ▸ bi
  have delta : (curve (f b)).Δ=f (curve b).Δ := by
    simp [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈,map_ofNat]
  have localgood : v (curve (f b)).Δ=0 := by rw [delta,agrees]; exact du
  obtain ⟨T,A,series⟩ := classicalInput (f b) large up localint localgood
  let G := (mapShortPoint f b).comp (AddMonoidHom.id (curve b).Point)
  let I := T.kernel.comap G
  let H : I →+ T.kernel := {
    toFun := fun Q => ⟨G Q.1,Q.2⟩
    map_zero' := Subtype.ext (map_zero G)
    map_add' := fun x y => Subtype.ext (map_add G x.1 y.1) }
  let log : I →+ L := (A.comp T.chart.toAddMonoidHom).comp H
  let trunc (j:ℤ) := logTrunc (shortDifferential b) 64 (parameter (j • P))
  have depths (j:ℤ) (hj:j≠0) (formal : (1:WithTop ℤ)≤u (reciprocal (j • P))) :
      ∃ mem : j • P ∈ I, ∃ d : ℤ, 0<d ∧ v (log ⟨j • P,mem⟩)=(d:WithTop ℤ) ∧
        ((d+64:ℤ):WithTop ℤ)≤v (log ⟨j • P,mem⟩-f (trunc j)) := by
    obtain ⟨nz,d,pos,ord⟩ := actual_depth u root bi hj formal
    have coords := mapShortPoint_coordinates f (j • P)
    have mem : j • P ∈ I := by
      apply T.membership
      · change 0<v (reciprocal (mapShortPoint f b (j • P)))
        rw [coords.2,agrees]
        exact lt_of_lt_of_le (by decide : (0:WithTop ℤ)<1) formal
      · change parameter (mapShortPoint f b (j • P))≠0
        rw [coords.1]; exact (map_ne_zero f).mpr nz
    let Q : I := ⟨j • P,mem⟩
    let Y := T.chart (H Q)
    have coord : T.coordinate Y=f (parameter (j • P)) := (T.chart_parameter (H Q)).trans coords.1
    have val : v (T.coordinate Y)=(d:WithTop ℤ) := by rw [coord,agrees,ord]
    have conv := series Y
    have order := series_order w large localint natOrd pos val conv
    have tail := log_trunc_error w (k:=64) large _ (shortDifferential_integral v localint) natOrd pos val conv
    refine ⟨mem,d,pos,order,?_⟩
    change _ ≤ v (A Y - f (logTrunc (shortDifferential b) 64 (parameter (j • P))))
    rw [map_shortTrunc,←coord]
    exact tail
  obtain ⟨mh,dh,_,oh,th⟩ := depths h denom fh
  by_cases zm : m=0
  · subst m
    simp [ordinaryRatio,parameter,logTrunc_zero]
  obtain ⟨mm,dm,_,om,tm⟩ := depths m zm fm
  have cross : h • (⟨m • P,mm⟩ : I)= m • (⟨h • P,mh⟩:I) := by
    apply Subtype.ext
    change h • (m • P) = m • (h • P)
    rw [←mul_zsmul,←mul_zsmul,mul_comm h m]
  have mul : (h:L)*log ⟨m • P,mm⟩=(m:L)*log ⟨h • P,mh⟩ := by
    simpa only [map_zsmul,zsmul_eq_mul] using congrArg log cross
  obtain ⟨_,eq,precision⟩ := cleared_ratio v (k:=64) (by decide) (intOrd h denom) (intOrd m zm)
    (by positivity) om oh tm th mul
  have lift (x:K) : v (algebraMap K L x)=discreteOrder (w.valuation K) x := completionOrder_algebraMap w x
  have eval : f (ordinaryRatio P m h)=f (trunc m)/f (trunc h) := map_div₀ f _ _
  have same : algebraMap K L (τ (ordinaryRatio P m h))=f (trunc m)/f (trunc h) := eval
  constructor
  · rw [←lift,←lift,same,map_div₀ (algebraMap K L),map_intCast,map_intCast]
    exact eq
  · rw [←lift,map_sub,map_mul,map_intCast,map_intCast,same]
    exact precision

end Sun28.Ordinary
#print axioms Sun28.Ordinary.shortDifferential_integral
#print axioms Sun28.Ordinary.map_shortTrunc
#print axioms Sun28.Ordinary.ordinary_index_ratio64
