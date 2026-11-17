import DyadicCharacter
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Frobenius
import Mathlib.Data.ZMod.QuotientRing

namespace Sun28.RayDensity.Artin
open Ideal

theorem gaussian_prime_of_norm {z:GaussianInt} {p:ℕ} (hp:p.Prime)
    (N:z.norm.natAbs=p) : Prime z := by
  apply Irreducible.prime
  constructor
  · intro u
    have h:=Zsqrtd.norm_eq_one_iff.mpr u
    exact hp.ne_one (N.symm.trans h)
  · intro a b e
    have n : a.norm.natAbs*b.norm.natAbs=p := by simpa [e,Zsqrtd.norm_mul,Int.natAbs_mul] using N
    rcases hp.eq_one_or_self_of_dvd a.norm.natAbs (n ▸ dvd_mul_right _ _) with h|h
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp h)
    · have h1 : b.norm.natAbs=1 := by rw [h] at n; exact (Nat.mul_right_inj hp.ne_zero).mp (by simpa using n)
      exact Or.inr (Zsqrtd.norm_eq_one_iff.mp h1)

/-- The principal ideal of a Gaussian generator of rational prime norm is a
prime ideal with residue field precisely F_p, even when the coordinates have signs. -/
noncomputable def gaussianResidue {z:GaussianInt} {p:ℕ} (hp:p.Prime) (N:z.norm.natAbs=p) :
    GaussianInt ⧸ Ideal.span {z} ≃+* ZMod p := by
  letI : Fact p.Prime := ⟨hp⟩
  have norm : z.re^2+z.im^2=(p:ℤ) := by
    have e:=congrArg ((↑):ℕ→ℤ) N
    rw [Int.natAbs_of_nonneg (GaussianInt.norm_nonneg _)] at e
    simpa [Zsqrtd.norm,sq] using e
  have znorm : (z.re:ZMod p)^2+(z.im:ZMod p)^2=0 := by
    have e:=congrArg (fun x:ℤ=>(x:ZMod p)) norm
    simpa only [Int.cast_add,Int.cast_pow,Int.cast_natCast,ZMod.natCast_self] using e
  have nonzero : (z.im:ZMod p)≠0 := by
    intro hy
    have hx : (z.re:ZMod p)=0 := by simpa [hy] using znorm
    obtain ⟨s,hs⟩:=(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hx
    obtain ⟨t,ht⟩:=(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hy
    have factor : (p:ℤ)*((p:ℤ)*(s^2+t^2))=(p:ℤ)*1 := by
      rw [hs,ht] at norm
      linear_combination norm
    have pp : (p:ℤ)≠0 := by exact_mod_cast hp.ne_zero
    have dvd : (p:ℤ)∣1 := ⟨s^2+t^2,mul_left_cancel₀ pp factor |>.symm⟩
    exact hp.not_dvd_one (by exact_mod_cast dvd)
  let r : ZMod p := -(z.re:ZMod p)/(z.im:ZMod p)
  have root : r*r=(-1:ℤ) := by
    dsimp [r]
    field_simp
    linear_combination znorm
  let ev : GaussianInt →+* ZMod p := Zsqrtd.lift ⟨r,root⟩
  have ez : ev z=0 := by
    change (z.re:ZMod p)+(z.im:ZMod p)*r=0
    dsimp [r]
    field_simp
    ring
  have maximal : (Ideal.span {z}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (gaussian_prime_of_norm hp N).irreducible
  have hle : Ideal.span {z} ≤ RingHom.ker ev :=
    (Ideal.span_singleton_le_iff_mem _).2 ez
  have eq : Ideal.span {z} = RingHom.ker ev := by
    exact maximal.eq_of_le (RingHom.ker_ne_top ev) hle
  have surjective : Function.Surjective ev := fun a=>⟨(a.val:GaussianInt),by
    rw [map_natCast,ZMod.natCast_zmod_val]⟩
  exact (Ideal.quotEquivOfEq eq).trans (RingHom.quotientKerEquivOfSurjective surjective)

theorem gaussian_degree_one {z:GaussianInt} {p:ℕ} (hp:p.Prime) (N:z.norm.natAbs=p) :
    Nat.card (GaussianInt ⧸ Ideal.span {z})=p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_congr (gaussianResidue hp N).toEquiv,Nat.card_eq_fintype_card,ZMod.card]

/-- A true relative arithmetic Frobenius, restricted to prime-to-p roots of
unity, acts with exponent p for a prime ideal lying over the actual (z). -/
theorem gaussian_frobenius {z:GaussianInt} {p m:ℕ} (hp:p.Prime) (N:z.norm.natAbs=p)
    {S:Type*} [CommRing S] [IsDomain S] [Algebra GaussianInt S] {Q:Ideal S}
    (above:Q.under GaussianInt=Ideal.span {z}) {σ:S→ₐ[GaussianInt] S}
    (fr:σ.IsArithFrobAt Q) {ζ:S} (torsion:ζ^m=1) (away:(m:S)∉Q) :
    σ ζ=ζ^p := by
  rw [fr.apply_of_pow_eq_one torsion away,above,gaussian_degree_one hp N]

end Sun28.RayDensity.Artin
#print axioms Sun28.RayDensity.Artin.gaussian_prime_of_norm
#print axioms Sun28.RayDensity.Artin.gaussianResidue
#print axioms Sun28.RayDensity.Artin.gaussian_degree_one
#print axioms Sun28.RayDensity.Artin.gaussian_frobenius
