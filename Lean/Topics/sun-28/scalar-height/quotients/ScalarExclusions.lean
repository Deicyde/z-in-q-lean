import ScalarKernels

namespace Sun28.ScalarQuotients
open Sun28.WitnessHeight
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

def values {n:ℕ} (A B:ZMod n) := (2*A+3*B)*(A+B)*(A-1199*B)*(64*A+439*B)

/-- Filter a finite set of candidate kernel pairs against the primitive residue classes. -/
def localPairs (p n:ℕ) [NeZero n] (h:p∣n) (d:ℤ) (C:Finset (ℕ×ℕ)) : Finset (ℕ×ℕ) :=
  let sqs:Finset (ZMod n):=Finset.univ.image fun u:ZMod n=>u^2
  let twists:=sqs.image fun z=>(d:ZMod n)*z
  let prim:=(sqs ×ˢ sqs).filter fun t=>
    ¬(ZMod.castHom h (ZMod p) t.1=0 ∧ ZMod.castHom h (ZMod p) t.2=0) ∧
      values t.1 t.2∈twists
  C.filter fun kl=>∃t∈prim,
    2*t.1+3*t.2∈sqs.image (fun z=>(kl.1:ZMod n)*z) ∧
    t.1+t.2∈sqs.image (fun z=>(kl.2:ZMod n)*z)

theorem mem_localPairs {a b d Y u v:ℤ} {k l:ℕ} (ab:a.natAbs.Coprime b.natAbs)
    (e:homogenized a b=d*Y^2) (ek:2*a^2+3*b^2=(k:ℤ)*u^2) (el:a^2+b^2=(l:ℤ)*v^2)
    (p n:ℕ) [NeZero n] (hp:p.Prime) (h:p∣n) {C:Finset (ℕ×ℕ)} (c:(k,l)∈C) :
    (k,l)∈localPairs p n h d C := by
  let _:Fact p.Prime:=⟨hp⟩
  let A:ZMod n:=(a:ZMod n)^2
  let B:ZMod n:=(b:ZMod n)^2
  have aa (r:ℤ) : (r:ZMod n)^2 ∈ Finset.univ.image (fun z:ZMod n=>z^2) :=
    Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
  have vE:values A B=(d:ZMod n)*(Y:ZMod n)^2:=by
    simpa [A,B,values,homogenized] using congrArg (Int.castRingHom (ZMod n)) e
  have vk:2*A+3*B=(k:ZMod n)*(u:ZMod n)^2:=by
    simpa [A,B] using congrArg (Int.castRingHom (ZMod n)) ek
  have vl:A+B=(l:ZMod n)*(v:ZMod n)^2:=by
    simpa [A,B] using congrArg (Int.castRingHom (ZMod n)) el
  have pr:¬(ZMod.castHom h (ZMod p) A=0 ∧ ZMod.castHom h (ZMod p) B=0):=by
    rintro ⟨a0,b0⟩
    have a':(a:ZMod p)=0:=by
      change ZMod.castHom h (ZMod p) ((a:ZMod n)^2)=0 at a0
      rw [map_pow,map_intCast] at a0
      exact sq_eq_zero_iff.mp a0
    have b':(b:ZMod p)=0:=by
      change ZMod.castHom h (ZMod p) ((b:ZMod n)^2)=0 at b0
      rw [map_pow,map_intCast] at b0
      exact sq_eq_zero_iff.mp b0
    have pa:=(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp a'
    have pb:=(ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp b'
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (by simpa using Int.natAbs_dvd_natAbs.mpr pa)
      (by simpa using Int.natAbs_dvd_natAbs.mpr pb)) ab
  apply Finset.mem_filter.mpr
  refine ⟨c,(A,B),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨aa a,aa b⟩,pr,?_⟩,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨_,aa Y,vE.symm⟩
  · exact Finset.mem_image.mpr ⟨_,aa u,vk.symm⟩
  · exact Finset.mem_image.mpr ⟨_,aa v,vl.symm⟩

def candidates (d:ℤ):Finset (ℕ×ℕ):=(14*d.natAbs).divisors ×ˢ (30*d.natAbs).divisors

private theorem first_unit : localPairs 2 16 (by decide) 1 (candidates 1)={(2,1)} := by decide
private theorem first_neg : localPairs 2 16 (by decide) (-1) (candidates (-1))={(2,1)} := by decide
private theorem plus_end : localPairs 3 9 (by decide) 1 {(2,1)}=∅ := by decide
private theorem minus_end : localPairs 5 25 (by decide) (-1) {(2,1)}=∅ := by decide

private theorem first_thirteen : localPairs 2 16 (by decide) 13 (candidates 13)=
    {(2,1),(2,65),(91,1),(91,5),(91,13),(91,65)} := by decide
private theorem second_thirteen : localPairs 3 9 (by decide) 13
    {(2,1),(2,65),(91,1),(91,5),(91,13),(91,65)}={(2,65)} := by decide
private theorem last_thirteen : localPairs 13 13 (by decide) 13 {(2,65)}=∅ := by decide

/-- The three signed octic twists have no rational affine point with nonzero ordinate. -/
theorem no_affine_point {x y:ℚ} {d:ℤ} (hd:d=1 ∨ d= -1 ∨ d=13) (yn:y≠0) :
    octic x ≠ (d:ℚ)*y^2 := by
  intro eq
  have sf:Squarefree d:=by
    rcases hd with rfl|rfl|rfl
    · exact squarefree_one
    · exact isUnit_neg_one.squarefree
    · exact (Nat.prime_iff_prime_int.mp (by decide:Nat.Prime 13)).squarefree
  obtain ⟨Y,e⟩:=integral_point sf yn eq
  have ab:x.num.natAbs.Coprime (x.den:ℤ).natAbs:=by simpa using x.reduced
  obtain ⟨k,l,u,v,hk,hl,ek,el⟩:=two_kernels ab (by exact_mod_cast x.den_nz) sf.ne_zero e
  have can:(k,l)∈candidates d:=Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hk,mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr sf.ne_zero)⟩,
    Nat.mem_divisors.mpr ⟨hl,mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr sf.ne_zero)⟩⟩
  have lift:=@mem_localPairs _ _ _ _ _ _ _ _ ab e ek el
  have first:=lift 2 16 (by decide) (by decide) can
  rcases hd with rfl|rfl|rfl
  · rw [first_unit] at first
    have t:=lift 3 9 (by decide) (by decide) first
    rw [plus_end] at t;exact Finset.notMem_empty _ t
  · rw [first_neg] at first
    have t:=lift 5 25 (by decide) (by decide) first
    rw [minus_end] at t;exact Finset.notMem_empty _ t
  · rw [first_thirteen] at first
    have t:=lift 3 9 (by decide) (by decide) first
    rw [second_thirteen] at t
    have s:=lift 13 13 (by decide) (by decide) t
    rw [last_thirteen] at s;exact Finset.notMem_empty _ s

theorem excluded_classes (x:ℚ) : scalarClass x≠1 ∧ scalarClass x≠ -1 ∧ scalarClass x≠13 := by
  obtain ⟨_,y,yn,eq⟩:=octic_twist x
  exact ⟨fun h=>no_affine_point (Or.inl h) yn eq,
    fun h=>no_affine_point (Or.inr (Or.inl h)) yn eq,fun h=>no_affine_point (Or.inr (Or.inr h)) yn eq⟩

end
end Sun28.ScalarQuotients
#print axioms Sun28.ScalarQuotients.mem_localPairs
#print axioms Sun28.ScalarQuotients.no_affine_point
#print axioms Sun28.ScalarQuotients.excluded_classes
