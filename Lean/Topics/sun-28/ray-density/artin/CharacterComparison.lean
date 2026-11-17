import PrimeArtin
import CyclotomicFrobenius

namespace Sun28.RayDensity.Artin
open IsCyclotomicExtension.Rat NumberField SemidirectProduct
noncomputable section
variable {I:Type*} (q:I→ℕ) [∀i,Fact (q i).Prime]

/-- Normalized residue tuple of the single integer a+bi, subject only to
the invertibility conditions required to form a unit. -/
def primeTuple (a b:ℤ) (h:((a:ZMod 16),(b:ZMod 16))∈primarySet)
    (unit:∀ i, (a:ZMod (q i))^2+(b:ZMod (q i))^2≠0) : RayUnits q :=
  (⟨((a:ZMod 16),(b:ZMod 16)),h⟩,fun i=>unitOf a b (unit i))

theorem representative_character {a b:ℤ} {p:ℕ} (N:a^2+b^2=(p:ℤ))
    (h:((a:ZMod 16),(b:ZMod 16))∈primarySet)
    (unit:∀ i, (a:ZMod (q i))^2+(b:ZMod (q i))^2≠0)
    (cop32:p.Coprime 32) (cop:∀ i,p.Coprime (q i)) :
    rationalCharacter q (inl (primeTuple q a b h unit)) =
      (ZMod.unitOfCoprime p cop32,fun i=>ZMod.unitOfCoprime p (cop i)) := by
  rw [character_on_even]
  apply Prod.ext
  · apply Units.ext
    change norm32 ((a:ZMod 16),(b:ZMod 16))=(p:ZMod 32)
    rw [norm32_integer,N,Int.cast_natCast]
  · apply funext
    intro i
    apply Units.ext
    change (unitOf (p:=q i) a b (unit i):GR (q i)).norm=(p:ZMod (q i))
    rw [norm_coordinates,val_unitOf]
    change (a:ZMod (q i))^2+(b:ZMod (q i))^2=(p:ZMod (q i))
    simpa only [Int.cast_add,Int.cast_pow,Int.cast_natCast] using congrArg (fun x:ℤ=>(x:ZMod (q i))) N

/-- At any prime of any cyclotomic number field above p, the computed
dyadic ray coordinate equals the image of genuine Frobenius in canonical Galois coordinates. -/
theorem dyadic_frobenius {a b:ℤ} {p:ℕ} [Fact p.Prime] (N:a^2+b^2=(p:ℤ))
    (h:((a:ZMod 16),(b:ZMod 16))∈primarySet)
    (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {32} ℚ K]
    (Q:Ideal (𝓞 K)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p:ℤ)})]
    (cop:p.Coprime 32) {σ:Gal(K/ℚ)} (fr:IsArithFrobAt ℤ σ Q) :
    galEquivZMod 32 K σ=dyadicNorm ⟨((a:ZMod 16),(b:ZMod 16)),h⟩ := by
  rw [galois_frobenius K Q cop fr]
  apply Units.ext
  change (p:ZMod 32)=norm32 ((a:ZMod 16),(b:ZMod 16))
  rw [norm32_integer,N,Int.cast_natCast]

/-- Compatibility for an entire tuple of odd local ray coordinates of a
single Gaussian prime generator, allowing the cyclotomic field and place to
differ at each modulus. -/
theorem odd_frobenius {a b:ℤ} {p:ℕ} [Fact p.Prime] (N:a^2+b^2=(p:ℤ))
    (h:((a:ZMod 16),(b:ZMod 16))∈primarySet)
    (cop32:p.Coprime 32) (cop:∀ i,p.Coprime (q i))
    (i:I) (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {q i} ℚ K]
    (Q:Ideal (𝓞 K)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p:ℤ)})]
    {σ:Gal(K/ℚ)} (fr:IsArithFrobAt ℤ σ Q) :
    ∃ unit:∀ j, (a:ZMod (q j))^2+(b:ZMod (q j))^2≠0,
      (rationalCharacter q (inl (primeTuple q a b h unit))).2 i=galEquivZMod (q i) K σ := by
  have one (j:I) : (a:ZMod (q j))^2+(b:ZMod (q j))^2=(p:ZMod (q j)) := by
    exact_mod_cast congrArg (fun x:ℤ=>(x:ZMod (q j))) N
  have unit (j:I) : (a:ZMod (q j))^2+(b:ZMod (q j))^2≠0 := by
    rw [one]
    exact (ZMod.unitOfCoprime p (cop j)).ne_zero
  refine ⟨unit,?_⟩
  rw [representative_character q N h unit cop32 cop,galois_frobenius K Q (cop i) fr]

end
end Sun28.RayDensity.Artin
#print axioms Sun28.RayDensity.Artin.representative_character
#print axioms Sun28.RayDensity.Artin.dyadic_frobenius
#print axioms Sun28.RayDensity.Artin.odd_frobenius
