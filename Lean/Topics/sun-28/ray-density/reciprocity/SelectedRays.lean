import RayCoordinates
import CharacterComparison
import CommonPrimes

namespace Sun28.Reciprocity
open Sun28.RayDensity Sun28.RayDensity.Artin Sun28.FinitePattern ManuscriptV15.Arithmetic
noncomputable section

/-- All odd rational primes at this cutoff, with the distinguished prime 7 at every cutoff. -/
abbrev Slot (L:ℕ) := {r:ℕ // r.Prime ∧ r≠2 ∧ (r≤L ∨ r=7)}

instance (L:ℕ) : Finite (Slot L) := by
  apply Finite.of_injective (fun r:Slot L=> (⟨r.val,by rcases r.2.2.2 with e|e <;> omega⟩ : Fin (L+8)))
  intro x y h
  exact Subtype.ext (congrArg Fin.val h)

noncomputable instance (L:ℕ) : Fintype (Slot L) := Fintype.ofFinite _

abbrev moduli (L:ℕ) := fun i:Slot L=>i.val
instance (L:ℕ) (i:Slot L) : Fact ((moduli L i).Prime) := ⟨i.2.1⟩

abbrev seven (L:ℕ) : Slot L := ⟨7,by decide,by decide,Or.inr rfl⟩

theorem level_coprime (L:ℕ) : Pairwise (Function.onFun Nat.Coprime (levels (moduli L))) := by
  have two (i:Slot L):Nat.Coprime 16 i.val := by
    change Nat.Coprime (2^4) i.val
    exact ((Nat.coprime_primes (by decide) i.2.1).2 (Ne.symm i.2.2.1)).pow_left 4
  rintro (_|i) (_|j) h
  · exact (h rfl).elim
  · exact two _
  · exact (two _).symm
  · exact (Nat.coprime_primes i.2.1 j.2.1).2 (fun e=>h (congrArg some (Subtype.ext e)))

def adjacent {r:ℕ} (v:GU r) (e:Bool) : ZMod r :=
  ((coords v).1 + (if e then 1 else -1))^2 + (coords v).2^2

/-- Only a finite ray-coordinate test. Its argument contains no Gaussian prime or generator. -/
def admissible (L:ℕ) (w:RayUnits (moduli L)) : Prop :=
  w.1.val=(9,0) ∧ coords (w.2 (seven L))=(1,3) ∧
    ∀ i:Slot L,i.val≠7 → ∀ e:Bool, adjacent (w.2 i) e≠0

theorem adjacent_test {r:ℕ} [Fact r.Prime] (a b:ℤ) (h:(a:ZMod r)^2+(b:ZMod r)^2≠0) (e:Bool) :
    adjacent (unitOf (p:=r) a b h) e≠0 ↔ ¬r∣adjacentNorm (a,b) e := by
  have eq : adjacent (unitOf (p:=r) a b h) e = (((a+(if e then 1 else -1))^2+b^2:ℤ):ZMod r) := by
    cases e <;> simp [adjacent,coords]
  rw [eq,ne_eq,ZMod.intCast_zmod_eq_zero_iff_dvd,Int.natCast_dvd]
  rfl

theorem admissible_generator (L:ℕ) (a b:ℤ) (dy:((a:ZMod 16),(b:ZMod 16))∈primarySet)
    (unit:∀ i:Slot L, (a:ZMod i.val)^2+(b:ZMod i.val)^2≠0) :
    admissible L (primeTuple (moduli L) a b dy unit) ↔
    gaussianCongruent 16 (a,b) (9,0) ∧ gaussianCongruent 7 (a,b) (1,3) ∧ clean L L (a,b) := by
  have ray (m:ℕ) (x y:ℤ) : ((a:ZMod m),(b:ZMod m))=((x:ZMod m),(y:ZMod m)) ↔
      gaussianCongruent m (a,b) (x,y) := by
    rw [Prod.mk.injEq]
    exact and_congr (ZMod.intCast_eq_intCast_iff ..) (ZMod.intCast_eq_intCast_iff ..)
  have h16:=ray 16 9 0
  have h7:=ray 7 1 3
  simp only [Int.cast_ofNat,Int.cast_zero,Int.cast_one] at h16 h7
  have u7 : (a:ZMod 7)^2+(b:ZMod 7)^2≠0 := unit (seven L)
  have coord7 : coords (unitOf (p:=7) a b u7)=((a:ZMod 7),(b:ZMod 7)) := by
    unfold coords
    rw [val_unitOf]
  unfold admissible
  change ((a:ZMod 16),(b:ZMod 16))=(9,0) ∧ coords (unitOf (p:=7) a b u7)=(1,3) ∧ _ ↔ _
  rw [coord7,h16,h7]
  apply and_congr_right;intro _
  apply and_congr_right;intro _
  constructor
  · intro good r hp h2 h7 le
    let _ : Fact r.Prime:=⟨hp⟩
    let i:Slot L:=⟨r,hp,h2,Or.inl le⟩
    exact ⟨(adjacent_test (r:=r) a b (unit i) true).1 (good i h7 true),
      fun _=>(adjacent_test (r:=r) a b (unit i) false).1 (good i h7 false)⟩
  · intro clean i h7 e
    have le:i.val≤L:=i.2.2.2.resolve_right h7
    have good:=clean i.val i.2.1 i.2.2.1 h7 le
    cases e
    · exact (adjacent_test a b (unit i) false).2 (good.2 le)
    · exact (adjacent_test a b (unit i) true).2 good.1

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.level_coprime
#print axioms Sun28.Reciprocity.adjacent_test
#print axioms Sun28.Reciprocity.admissible_generator
