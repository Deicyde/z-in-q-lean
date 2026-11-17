import IntegralEntries
import ExceptionalTrace
import ZInQKernel.Model.Heights.DuplicationBounds

/-! Passing from prime elements to arbitrary finite places over the rational prime. -/
namespace Sun28.OrdinaryIntegrality
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.Ordinary Sun28.ScalarTrace Sun28.FixedPreparation Sun28.Forward Sun28.WitnessIndices
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

/-- If every prime element above q has nonnegative order, the reduced denominator
over the Euclidean ring of integers is coprime to q. Any additive valuation
positive on q therefore gives a nonnegative order as well. -/
theorem integral_of_prime_elements {q : ℕ} (v : AddValuation K0 (WithTop ℤ))
    (positive : Vge v 1 (q:K0)) {x : K0}
    (above : ∀ π : Zs,∀ prime : Prime π,π∣(q:Zs) → Vge (vP π prime) 0 x) : Vge v 0 x := by
  by_cases zero : x=0
  · subst x; exact Vge.zero _
  obtain ⟨a,b,bn,coprime,eq⟩:=exists_coprime_fraction x
  have an : a≠0 := by rintro rfl; simp at eq; exact zero eq
  have cop : IsCoprime (q:Zs) b := by
    apply isCoprime_of_prime_dvd (fun h=>bn h.2)
    intro π prime divides den
    have num : ¬π∣a := fun ad=>prime.not_isUnit (coprime.isUnit_of_dvd' ad den)
    have ge:=above π prime divides
    unfold Vge at ge
    rw [vP_apply prime zero,eq,vp_div prime (toK0_ne_zero an) (toK0_ne_zero bn),
      (vp_eq_zero_iff prime an).mpr num] at ge
    have neg : 0 < vp π (Zs.toK0 b) := (vp_pos_iff prime bn).mpr den
    norm_cast at ge
    omega
  have natural (a : Zs) : Vge v 0 (Zs.toK0 a) := by
    have root : Vge v 0 sqrt2 := by
      obtain ⟨j,hj⟩:=val_eq_coe (v:=v) (show sqrt2≠0 by intro h; simpa [h] using sqrt2_sq)
      have sq:=vge_ofNat (v:=v) 2
      unfold Vge at sq ⊢
      rw [←sqrt2_sq,val_pow_coe hj 2] at sq
      norm_cast at sq
      rw [hj]
      exact WithTop.coe_le_coe.mpr (by omega)
    have re := K0.eq_re_add_im_mul_sqrt2 (Zs.toK0 a)
    rw [re]
    simp only [Zs.toK0_re,Zs.toK0_im,Rat.cast_intCast]
    exact (vge_intCast a.re).add ((vge_intCast a.im).mul root)
  obtain ⟨r,s,bez⟩:=cop
  have unit : v (Zs.toK0 b)=0 := by
    by_contra nz
    obtain ⟨j,hj⟩:=val_eq_coe (v:=v) (toK0_ne_zero bn)
    have bge : 0≤j := WithTop.coe_le_coe.mp (hj ▸ (natural b) : (0:WithTop ℤ)≤(j:WithTop ℤ))
    have bpos : 1≤j := by
      by_contra! less
      have jz : j=0 := by omega
      exact nz (by simpa [jz] using hj)
    have smallB : Vge v 1 (Zs.toK0 b) := (Vge.of_eq hj).mono bpos
    have z := ((natural r).mul positive).add ((natural s).mul smallB)
    have eq1 := congrArg Zs.toK0 bez
    simp only [map_add,map_mul,map_one,map_natCast] at eq1
    change Vge v 1 _ at z
    rw [eq1] at z
    rw [Vge,v.map_one] at z
    exact (by decide : ¬ ((1:ℤ):WithTop ℤ) ≤ (0:WithTop ℤ)) z
  rw [eq]
  exact (natural a).div_unit unit

theorem ordinaryAt_integral {q : ℕ} [hp : Fact q.Prime] (fixed : q∈primes)
    (place : HeightOneSpectrum (𝓞 K0))
    [place.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨q,hp.out⟩).asIdeal]
    {w : NinePoints} {M c a} (rep : Consequences w M c a) (β : ℤ)
    (hc : anchor∣c) (hh : anchor∣a.h) (labels : ∀ j,a.m j=a.h*a.n j) :
    Exceptional.IntegralAtBoth place (ordinaryAt w M c (β:ℚ)) := by
  let p:=(Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨q,hp.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv p).1=q :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨q,hp.out⟩)
  have val:=prime_order_rat p place (q:=(q:ℚ)) (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  rw [name,padicValRat.self hp.out.one_lt,mul_one,map_natCast] at val
  have ep:=Ideal.ramificationIdx_pos_of_isDedekindDomain' place.asIdeal p.ne_bot
  have positive : Vge (discreteOrder (place.valuation K0)) 1 (q:K0) := by
    rw [Vge,val];exact_mod_cast ep
  have small : q≤23 := by
    have finite : ∀ n∈primes,n≤23 := by decide
    exact finite _ fixed
  intro i
  constructor
  · exact integral_of_prime_elements _ positive (fun π hπ above=>(points_prime small hπ above rep β hc hh labels i).1)
  · exact integral_of_prime_elements _ positive (fun π hπ above=>(points_prime small hπ above rep β hc hh labels i).2)

end
#print axioms integral_of_prime_elements
#print axioms ordinaryAt_integral
end Sun28.OrdinaryIntegrality
