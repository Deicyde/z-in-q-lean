import KummerLaw
import KummerBoundary
import Mathlib.NumberTheory.Zsqrtd.Basic

namespace EllipticOrbit.KummerBoundary

open EllipticOrbit.Law
variable {K : Type*} [Field K] [DecidableEq K] {D : K}

/-- One integral equation for the three abscissas of actual Mathlib points.
All vertical, diagonal, torsion and infinity arguments are included by the
three simultaneous biquadratic identities. No nonzero abscissa is assumed. -/
theorem actual_triple (P Q : (curve D).Point) {a b c e A B : K}
    (p : Rep P a b) (q : Rep Q c e) (sum : Rep (P+Q) A B) :
    triple D (a,b) (c,e) (A,B) := by
  obtain ⟨s,_,top,mid,bot⟩:=symmetric_rep P Q p q sum (canonical_rep (P-Q))
  dsimp [triple]
  linear_combination B^2*top - A*B*mid + A^2*bot

/-- Where the coefficient vanishes, two nonzero numerators cannot add
to a zero numerator. Thus one initial Bézout identity handles every index. -/
theorem coefficient_coprime {R : Type*} [CommRing R] (d : R) (A B : ℕ → R)
    (primitive : ∀ k, IsCoprime (A k) (B k)) (origin : B 0=0)
    (seed : IsCoprime (A 1) d)
    (step : ∀ k, triple d (A k,B k) (A 1,B 1) (A (k+1),B (k+1))) (n : ℕ) :
    IsCoprime (A n) d := by
  by_contra fail
  have proper : Ideal.span ({A n,d} : Set R) ≠ ⊤ := by
    intro top
    exact fail (Ideal.mem_span_pair.mp ((Ideal.eq_top_iff_one _).mp top))
  obtain ⟨M,maximal,inc⟩ := Ideal.exists_le_maximal _ proper
  letI : M.IsMaximal := maximal
  letI : M.IsPrime := maximal.isPrime
  have an : A n∈M := inc (Ideal.subset_span (by simp))
  have dm : d∈M := inc (Ideal.subset_span (by simp))
  let f := Ideal.Quotient.mk M
  have dz : f d=0 := Ideal.Quotient.eq_zero_iff_mem.mpr dm
  have first : f (A 1)≠0 := fun z=>Ideal.IsPrime.notMem_of_isCoprime_of_mem seed
    (Ideal.Quotient.eq_zero_iff_mem.mp z) dm
  have live (k : ℕ) : f (A k)≠0 := by
    induction k with
    | zero =>
      intro z
      exact Ideal.IsPrime.notMem_of_isCoprime_of_mem (primitive 0)
        (Ideal.Quotient.eq_zero_iff_mem.mp z) (by rw [origin]; exact M.zero_mem)
    | succ k ih =>
      intro z
      have unit : f (B (k+1))≠0 := fun e=>Ideal.IsPrime.notMem_of_isCoprime_of_mem (primitive _)
        (Ideal.Quotient.eq_zero_iff_mem.mp z) (Ideal.Quotient.eq_zero_iff_mem.mp e)
      have h : (f (A k)*f (A 1)*f (B (k+1)))^2=0 := by
        simpa only [triple,map_add,map_mul,map_pow,map_ofNat,dz,z,mul_zero,zero_mul,
          add_zero,zero_add] using congrArg f (step k)
      exact (pow_ne_zero _ (mul_ne_zero (mul_ne_zero ih first) unit)) h
  exact live n (Ideal.Quotient.eq_zero_iff_mem.mpr an)

/-- Coprimality with a coefficient passes from a known representation of the
marked abscissa to any primitive representation of the same point. -/
theorem seed_of_cross {R : Type*} [CommRing R] (d a b A B : R) (pr : IsCoprime A B)
    (safe : IsCoprime a d) (cross : A*b=a*B) : IsCoprime A d := by
  obtain ⟨u,v,h⟩:=pr
  obtain ⟨s,t,hs⟩:=safe
  refine ⟨s*(a*u+b*v),t,?_⟩
  calc
    s*(a*u+b*v)*A+t*d = s*a*(u*A+v*B)+t*d := by linear_combination s*v*cross
    _ = 1 := by rw [h,mul_one,hs]

/-- One primitive homogeneous coordinate family on the actual elliptic group.
Only the fixed marked point's coefficient-prime certificate is needed. -/
theorem actual_four_coprime {R : Type*} [CommRing R] (f : R →+* K)
    (inj : Function.Injective f) (d : R) (P : (curve (f d)).Point)
    (A B : ℕ → R) (rep : ∀ k, Rep (k • P) (f (A k)) (f (B k)))
    (primitive : ∀ k, IsCoprime (A k) (B k))
    (a b : R) (marked : Rep P (f a) (f b)) (fixed : IsCoprime a d)
    (n : Fin 4 → ℤ) (i : Fin 4) (odd : ∀ j, j≠i → n j%2=1) :
    IsCoprime (A (n i).natAbs) (∏ j, B (n j).natAbs) := by
  have origin : B 0=0 := by
    have r0 : Rep (0 : (curve (f d)).Point) (f (A 0)) (f (B 0)) := by simpa using rep 0
    apply inj
    simpa only [map_zero] using (rep_zero.mp r0).2
  have seed : IsCoprime (A 1) d := by
    apply seed_of_cross d a b _ _ (primitive 1) fixed
    apply inj
    rw [map_mul,map_mul]
    have r1 : Rep P (f (A 1)) (f (B 1)) := by simpa using rep 1
    obtain ⟨s,_,sa,sb⟩:=r1
    obtain ⟨t,_,ta,tb⟩:=marked
    rw [sa,sb,ta,tb]; ring
  have rows (u v : ℕ) : triple d (A u,B u) (A v,B v) (A (u+v),B (u+v)) := by
    have plus : Rep (u • P+v • P) (f (A (u+v))) (f (B (u+v))) := by
      simpa only [add_nsmul] using rep (u+v)
    have tri:=actual_triple (u • P) (v • P) (rep u) (rep v) plus
    apply inj
    simpa only [triple,map_add,map_mul,map_pow,map_ofNat] using tri
  exact four_coprime d (fun k=>(A k,B k)) n i primitive origin
    (coefficient_coprime d A B primitive origin seed (fun k=>rows k 1) _) odd rows

/-- The fixed marked numerator is coprime to 11−6√2 in the actual order. -/
theorem physical_seed : IsCoprime (⟨57,-28⟩ : Zsqrtd (2:ℤ)) (⟨11,-6⟩ : Zsqrtd (2:ℤ)) :=
  ⟨2-(⟨57,-28⟩ : Zsqrtd (2:ℤ)),(⟨16,-4⟩ : Zsqrtd (2:ℤ))^2,by decide⟩

#print axioms physical_seed
#print axioms actual_triple
#print axioms coefficient_coprime
#print axioms seed_of_cross
#print axioms actual_four_coprime
end EllipticOrbit.KummerBoundary
