import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Sun28.OcticResidues
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def f {R:Type*} [CommRing R] (X Y:R) := 52822*X-Y
def g {R:Type*} [CommRing R] (X Y:R) := 7203*X+109*Y
def h {R:Type*} [CommRing R] (X Y:R) := 380476866*X^2-837949*X*Y-109*Y^2

def candidates : Finset (ℤ×ℤ) :=
  let K:=(154:ℕ).divisors.image (fun u:ℕ=>(u:ℤ))
  (K∪K.image (fun u=> -u)) ×ˢ ((4578:ℕ).divisors.image (fun v:ℕ=>(v:ℤ)))

def test (p n:ℕ) [NeZero n] (pn:p∣n) (C:Finset (ℤ×ℤ)) :=
  let sqs:Finset (ZMod n):=Finset.univ.image (fun x:ZMod n=>x^2)
  let prim:=(sqs ×ˢ sqs).filter fun t=>
    ¬(ZMod.castHom pn (ZMod p) t.1=0 ∧ ZMod.castHom pn (ZMod p) t.2=0)
  C.filter fun ij=>∃t∈prim,
    f t.1 t.2∈sqs.image (fun z=>(ij.1:ZMod n)*z) ∧
    g t.1 t.2∈sqs.image (fun z=>(ij.2:ZMod n)*z) ∧
    7*(ij.1:ZMod n)*ij.2*h t.1 t.2∈sqs

private theorem mem_test {a b i j U V W:ℤ} (ab:a.natAbs.Coprime b.natAbs)
    (e:f (a^2) (b^2)=i*U^2) (z:g (a^2) (b^2)=j*V^2) (w:7*i*j*h (a^2) (b^2)=W^2)
    (p n:ℕ) [NeZero n] (hp:p.Prime) (pn:p∣n) {C:Finset (ℤ×ℤ)} (c:(i,j)∈C) :
    (i,j)∈test p n pn C := by
  let _:Fact p.Prime:=⟨hp⟩
  let A:ZMod n:=(a:ZMod n)^2
  let B:ZMod n:=(b:ZMod n)^2
  have sq (r:ℤ) : (r:ZMod n)^2∈Finset.univ.image (fun z:ZMod n=>z^2) :=
    Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
  have red (r:ℤ) (atp:ZMod.castHom pn (ZMod p) ((r:ZMod n)^2)=0) : p∣r.natAbs:=by
    rw [map_pow,map_intCast] at atp
    simpa using Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd r p).mp (sq_eq_zero_iff.mp atp))
  apply Finset.mem_filter.mpr
  refine ⟨c,(A,B),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨sq a,sq b⟩,?_⟩,?_,?_,?_⟩
  · rintro ⟨pa,pb⟩
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (red a pa) (red b pb)) ab
  · exact Finset.mem_image.mpr ⟨_,sq U,by simpa [A,B,f] using congrArg (Int.castRingHom (ZMod n)) e.symm⟩
  · exact Finset.mem_image.mpr ⟨_,sq V,by simpa [A,B,g] using congrArg (Int.castRingHom (ZMod n)) z.symm⟩
  · convert sq W using 1
    simpa [A,B,h] using congrArg (Int.castRingHom (ZMod n)) w

private def filtered : Finset (ℤ×ℤ) :=
  ({-11,77}:Finset ℤ) ×ˢ ({2,6,14,42,218,654,1526,4578}:Finset ℤ)

private theorem at_two : test 2 32 (by decide) candidates=filtered := by decide
private theorem at_three : test 3 27 (by decide) filtered=∅ := by decide

theorem no_integral_cells {a b i j U V W:ℤ} (ab:a.natAbs.Coprime b.natAbs) (c:(i,j)∈candidates)
    (e:f (a^2) (b^2)=i*U^2) (z:g (a^2) (b^2)=j*V^2) (w:7*i*j*h (a^2) (b^2)=W^2) : False := by
  have vis:=mem_test ab e z w 2 32 (by decide) (by decide) c
  rw [at_two] at vis
  have hit:=mem_test ab e z w 3 27 (by decide) (by decide) vis
  rw [at_three] at hit
  simp at hit

end
end Sun28.OcticResidues
#print axioms Sun28.OcticResidues.no_integral_cells
