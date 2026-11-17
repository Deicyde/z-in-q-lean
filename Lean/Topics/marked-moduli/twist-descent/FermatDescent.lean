import PrimitiveNorm

/-! The two coprime cubic coordinates of a nonbranch rational point give an
integral generalized Fermat equation of signature (4,4,3). -/
open ZInQ ZInQBlueprint.OddSupport
namespace ZInQBlueprint.TwistDescent

/-- A signed squarefree integer in the rational square class of a nonzero
integer divides that integer. Rational square factors may have denominators. -/
theorem squareclass_dvd {w t : ℤ} (hw : Squarefree w) (ht : t≠0) {v z : ℚ}
    (hv : v≠0) (hz : z≠0) (eq : (w:ℚ)*v^2=(t:ℚ)*z^2) : w.natAbs ∣ t.natAbs := by
  have sw := Int.squarefree_natAbs.mpr hw
  rw [←Nat.prod_primeFactors_of_squarefree sw]
  apply (Nat.prod_primeFactors_dvd_iff (by simpa using ht)).mpr
  intro p hp
  obtain ⟨prime,pw,_⟩ := Nat.mem_primeFactors.mp hp
  let _ : Fact p.Prime := ⟨prime⟩
  have odd := (squarefree_odd_order hw).mp pw
  have h := congrArg (padicValRat p) eq
  rw [padicValRat.mul (by exact_mod_cast hw.ne_zero) (pow_ne_zero _ hv),
    padicValRat.mul (by exact_mod_cast ht) (pow_ne_zero _ hz),padicValRat.pow,padicValRat.pow] at h
  refine Nat.mem_primeFactors.mpr ⟨prime,?_,by simpa using ht⟩
  by_contra hdiv
  have zero : padicValRat p (t:ℚ)=0 := by
    rw [padicValRat.of_int,padicValInt,←Nat.factorization_def _ prime,
      Nat.factorization_eq_zero_of_not_dvd hdiv]
    rfl
  obtain ⟨c,hc⟩ := odd
  rw [zero] at h
  push_cast at h
  omega

/-- Every reduced abscissa gives coprime, signed squarefree coefficients.
Neither the inverse coordinate exclusion x≠5 nor a sign restriction on d is needed. -/
theorem fermat_descent {d : ℤ} {x y : ℚ} (hd : d≠0) (hy : y≠0)
    (point : 30*(d:ℚ)*y^2=quintic x) :
    ∃ k r s m n T : ℤ, (k=1 ∨ k=2) ∧ Squarefree r ∧ Squarefree s ∧
      r.natAbs.Coprime s.natAbs ∧ m≠0 ∧ n≠0 ∧ m.natAbs.Coprime n.natAbs ∧
      r.natAbs*s.natAbs ∣ 30*d.natAbs ∧
      r^2*m^4+27*s^2*n^4=T^3 ∧
      (k^2)*T=quadraticNorm x.num x.den ∧
      k^3*(r*m^2)=realCubic x.num x.den ∧ k^3*(s*n^2)=imaginaryCubic x.num x.den := by
  obtain ⟨k,P,Q,T,hk,p,q,t,cop,norm⟩ :=
    primitive_norm x.num (x.den:ℤ) (by simpa using x.reduced)
  obtain ⟨m,r,pm,sr⟩ := exists_sq_mul_squarefree P
  obtain ⟨n,s,qn,ss⟩ := exists_sq_mul_squarefree Q
  rw [mul_comm (m^2) r] at pm
  rw [mul_comm (n^2) s] at qn
  have prod := product_at_twist point
  rw [←p,←q,←pm,←qn] at prod
  have bn : (x.den:ℚ)≠0 := by exact_mod_cast x.den_nz
  have yb := mul_ne_zero hy (pow_ne_zero 3 bn)
  have dq : (d:ℚ)≠0 := by exact_mod_cast hd
  have pn : (30:ℚ)*(d:ℚ)*(y*(x.den:ℚ)^3)^2≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) dq) (pow_ne_zero 2 yb)
  have mn : m≠0 := by intro e; subst m; apply pn; simpa using prod.symm
  have nn : n≠0 := by intro e; subst n; apply pn; simpa using prod.symm
  have rd : r ∣ P := ⟨m^2,pm.symm⟩
  have sd : s ∣ Q := ⟨n^2,qn.symm⟩
  have md : m ∣ P := ⟨r*m, by rw [←pm]; ring⟩
  have nd : n ∣ Q := ⟨s*n, by rw [←qn]; ring⟩
  have rs := Nat.Coprime.of_dvd (Int.natAbs_dvd_natAbs.mpr rd) (Int.natAbs_dvd_natAbs.mpr sd) cop
  have copmn := Nat.Coprime.of_dvd (Int.natAbs_dvd_natAbs.mpr md) (Int.natAbs_dvd_natAbs.mpr nd) cop
  have sf := squarefree_mul_iff.mpr ⟨(Int.isCoprime_iff_nat_coprime.mpr rs).isRelPrime,sr,ss⟩
  have kn : k≠0 := by rcases hk with h|h <;> simp [h]
  have link : ((r*s:ℤ):ℚ)*((k:ℚ)^3*m*n)^2=((30*d:ℤ):ℚ)*(y*(x.den:ℚ)^3)^2 := by
    push_cast at prod ⊢
    linear_combination prod
  have div := squareclass_dvd sf (show (30:ℤ)*d≠0 by exact mul_ne_zero (by norm_num) hd)
    (show ((k:ℚ)^3*m*n)≠0 by exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast kn)) (by exact_mod_cast mn)) (by exact_mod_cast nn))
    yb link
  refine ⟨k,r,s,m,n,T,hk,sr,ss,rs,mn,nn,copmn,by simpa only [Int.natAbs_mul,show (30:ℤ).natAbs=30 by decide] using div,?_,t,by rwa [pm],by rwa [qn]⟩
  rw [←pm,←qn] at norm
  linear_combination norm

#print axioms squareclass_dvd
#print axioms fermat_descent
end ZInQBlueprint.TwistDescent
