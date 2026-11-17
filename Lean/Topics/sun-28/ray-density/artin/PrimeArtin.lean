import GaussianPrimeIdeal
import CyclotomicCharacter
import CommonPrimes

namespace Sun28.RayDensity.Artin
open ManuscriptV15.Arithmetic Sun28.FinitePattern

/-- A residue restriction on the integer prime is weaker than choosing a
Gaussian representative in the specified two rays. -/
theorem integer_base_ray {p:ℕ} {w:Gaussian} (n:gaussianNorm w=p)
    (h16:gaussianCongruent 16 w (9,0)) (h7:gaussianCongruent 7 w (1,3)) :
    p ≡ 17 [MOD 224] := by
  have hn : w.1^2+w.2^2=(p:ℤ) := by
    change (w.1^2+w.2^2).natAbs=p at n
    have e:=congrArg ((↑):ℕ→ℤ) n
    rwa [Int.natAbs_of_nonneg (by positivity : 0≤ w.1^2+w.2^2)] at e
  have x : (w.1:ZMod 16)=(9:ZMod 16) := by
    simpa using (ZMod.intCast_eq_intCast_iff ..).2 h16.1
  have y : (w.2:ZMod 16)=(0:ZMod 16) := by
    simpa using (ZMod.intCast_eq_intCast_iff ..).2 h16.2
  have lifted:=norm32_integer w.1 w.2
  rw [x,y,hn] at lifted
  have dy : (p:ZMod 32)=(17:ZMod 32) := by
    change (p:ZMod 32)=norm32 (9,0)
    exact_mod_cast lifted.symm
  have s : (p:ℤ) ≡ 3 [ZMOD 7] := hn ▸ ((h7.1.pow 2).add (h7.2.pow 2)).trans (by decide)
  have e32 : p≡17 [MOD 32] := (ZMod.natCast_eq_natCast_iff ..).mp dy
  have e7 : p≡17 [MOD 7] := (Int.natCast_modEq_iff.mp s).trans (by decide : 3≡17 [MOD 7])
  exact (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 32 7)).1 ⟨e32,e7⟩

/-- The integer row b_0=241 satisfies all four fixed rational congruences
for arbitrary signed coefficients c and arbitrary progressions v=0 mod 3360. -/
theorem progression_base {u v:ℤ} (hu:u ≡ 241 [ZMOD 3360]) (hv:v ≡ 0 [ZMOD 3360]) (c:ℤ) :
    let n:=u+c*v^2
    n ≡ 17 [ZMOD 32] ∧ n ≡ 3 [ZMOD 7] ∧ n ≡ 1 [ZMOD 3] ∧ n ≡ 1 [ZMOD 5] := by
  have e : u+c*v^2 ≡ 241 [ZMOD 3360] := by
    simpa using hu.add ((Int.ModEq.refl c).mul (hv.pow 2))
  exact ⟨(e.of_dvd (by decide : (32:ℤ)∣3360)).trans (by decide),
         (e.of_dvd (by decide : (7:ℤ)∣3360)).trans (by decide),
         (e.of_dvd (by decide : (3:ℤ)∣3360)).trans (by decide),
         (e.of_dvd (by decide : (5:ℤ)∣3360)).trans (by decide)⟩

theorem char_away {S:Type*} [CommRing S] [Algebra GaussianInt S] {z:GaussianInt}
    {p m:ℕ} (hp:p.Prime) (N:z.norm.natAbs=p) {Q:Ideal S} (above:Q.under GaussianInt=Ideal.span {z})
    (cop:p.Coprime m) : (m:S)∉Q := by
  intro h
  have mem : (m:GaussianInt)∈Q.under GaussianInt := by
    change algebraMap GaussianInt S (m:GaussianInt) ∈ Q
    simpa using h
  rw [above] at mem
  have zero:=congrArg (gaussianResidue hp N) ((Ideal.Quotient.eq_zero_iff_mem).2 mem)
  have equal : (m:ZMod p)=0 := by
    simpa only [map_zero,map_natCast] using zero
  have dvd:= (ZMod.natCast_eq_zero_iff m p).1 equal
  exact (hp.coprime_iff_not_dvd.mp cop) dvd

/-- Every prime in the actual integer selection admits an oriented, degree-one
Gaussian prime ideal, and its arithmetic Frobenius acts by p on all
prime-to-p roots of unity in any coefficient algebra which is a domain. -/
theorem common_prime_frobenius {L p:ℕ} (h:commonPrime L L p) :
    p ≡ 17 [MOD 224] ∧ ∃ z:GaussianInt,
      gaussianCongruent 16 (z.re,z.im) (9,0) ∧ gaussianCongruent 7 (z.re,z.im) (1,3) ∧
      clean L L (z.re,z.im) ∧ Prime z ∧ Nat.card (GaussianInt ⧸ Ideal.span {z})=p ∧
      ∀ {S:Type} [CommRing S] [IsDomain S] [Algebra GaussianInt S] {Q:Ideal S},
        Q.under GaussianInt=Ideal.span {z} → ∀ {σ:S→ₐ[GaussianInt] S}, σ.IsArithFrobAt Q →
        ∀ {m:ℕ}, p.Coprime m → ∀ {ζ:S}, ζ^m=1 → σ ζ = ζ^p := by
  obtain ⟨prime,w,hn,u,v,clean_w⟩:=h
  let z:GaussianInt:=⟨w.1,w.2⟩
  have N : z.norm.natAbs=p := by simpa [z,Zsqrtd.norm,gaussianNorm,sq] using hn
  refine ⟨integer_base_ray hn u v,z,u,v,clean_w,gaussian_prime_of_norm prime N,gaussian_degree_one prime N,?_⟩
  intro S _ _ _ Q hov σ fr m cop ζ torsion
  exact gaussian_frobenius prime N hov fr torsion (char_away prime N hov cop)

end Sun28.RayDensity.Artin
#print axioms Sun28.RayDensity.Artin.integer_base_ray
#print axioms Sun28.RayDensity.Artin.progression_base
#print axioms Sun28.RayDensity.Artin.char_away
#print axioms Sun28.RayDensity.Artin.common_prime_frobenius
