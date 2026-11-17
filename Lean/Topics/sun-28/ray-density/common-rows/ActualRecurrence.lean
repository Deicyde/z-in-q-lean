import SharedSelection
import QualitativePattern

namespace Sun28.CommonRows
open Finset Sun28.PrimeTransfer Sun28.RayDensity Sun28.RayDensity.Artin Sun28.Reciprocity
open Sun28.FinitePattern Sun28.PrimeValues Sun28.PrimeClasses Sun28.ContactFactors Sun28.PrimeLower
open ManuscriptV15.Arithmetic
open scoped Classical
noncomputable section

/-- The primary generator in the distinguished ray is i at every additional
odd prime through its level, so its rational norm is one there. -/
theorem fixed_norm_residue {L p r:ℕ} (hp:p.Prime) (odd:p≠2) (away:p≠7) (le:p≤L)
    (member:oneClass L r) : (r:ZMod p)=1 := by
  obtain ⟨_,J,card,ray⟩:=member
  obtain ⟨z,dy,unit,_,sz,coord⟩:=prime_ideal_data (moduli L) (level_coprime L) J
  let slot:Slot L:=⟨p,hp,odd,Or.inl le⟩
  have word:primeTuple (moduli L) z.re z.im dy unit=fixedWord L:=coord.symm.trans ray
  have localEq:=congrArg (fun v:RayUnits (moduli L)=>coords (v.2 slot)) word
  have xy:((z.re:ZMod p),(z.im:ZMod p))=(0,1):=by
    simpa [slot,primeTuple,fixedWord,fixedOdd,away,coords] using localEq
  have norm : z.norm=(r:ℤ) := by
    rw [←abs_of_nonneg (GaussianInt.norm_nonneg z),←Int.natCast_natAbs]
    exact_mod_cast sz.symm.trans card
  have norm' : z.re^2+z.im^2=(r:ℤ) := by
    simpa [Zsqrtd.norm,pow_two] using norm
  have eq := congrArg (fun a:ℤ=>(a:ZMod p)) norm'
  have xx : (z.re:ZMod p)=0:=congrArg Prod.fst xy
  have yy : (z.im:ZMod p)=1:=congrArg Prod.snd xy
  simpa [xx,yy] using eq.symm

/-- At any fixed inert p outside K, the published one-class narrow recurrence
gives arbitrarily large genuine configurations rejected by the old sentinel.
The conclusion tests the actual signed orders at *all* additional primes through p. -/
theorem narrow_recovered (narrow:NarrowClassRecurrence) (A:Fin 3→ℚ)
    {K p:ℕ} (seven:7≤K) (lower:K<p) (prime:p.Prime) (inert:p%4=3)
    (d H Y:ℕ) (dp:0<d) :
    ∃ u w:ℕ,0<w ∧ d∣w ∧ H*((dilation A)*w)^2<u ∧
      (∀i:↥(shifts A),∃r>Y,(r:ℤ)=form A (u,w) i ∧ oneClass p r) ∧
      patternWeight A K K (u,w)≠0 ∧ obstruction A p (u,w) ∧ collisions A K p (u,w)=0 := by
  have strong : ∀(K Y H d:ℕ),0<d→∃u w:ℕ,0<w ∧ d∣w ∧ H*((dilation A)*w)^2<u ∧
    ∀i:↥(shifts A),∃r>Y,(r:ℤ)=form A (u,w) i ∧ oneClass K r := by
    intro K Y H d dp
    let C:=(shifts A).image fun r=>offset (dilation A) r*(d:ℤ)^2
    let B:=C.sup Int.natAbs+H*((dilation A)*d)^2+Y+1
    have bp:0<B:=by dsimp [B];omega
    obtain ⟨u,large,m,mp,quartic,seq⟩:=narrow K C (4*B^2)
    have safe:B*m^2+B<u:=by
      by_cases small:m^2≤ B
      · have v:=Nat.mul_le_mul_left B small
        nlinarith only [large,v,bp,Nat.le_mul_self B]
      · have v:B+1≤ m^2:=by omega
        have h:=Nat.mul_le_mul_right (m^2) v
        nlinarith only [quartic,h,large,show 2≤ m^2 by omega]
    refine ⟨u,d*m,Nat.mul_pos dp mp,dvd_mul_right ..,?_,fun i=>?_⟩
    · have le:H*((dilation A)*d)^2≤ B:=by dsimp [B];omega
      nlinarith only [safe,Nat.mul_le_mul_right (m^2) le]
    let h:=offset (dilation A) i*(d:ℤ)^2
    have mem:h∈C:=mem_image_of_mem _ i.property
    have size:h.natAbs≤ B:=(le_sup (f:=Int.natAbs) mem).trans (by dsimp [B];omega)
    obtain ⟨r,eq,ok⟩:=seq h mem
    have low:-(B:ℤ)≤h:=by omega
    have gap:(B:ℤ)*(m:ℤ)^2+B<(u:ℤ):=by exact_mod_cast safe
    have gt:(Y:ℤ)<r:=by
      have yB:Y≤ B:=by dsimp [B];omega
      nlinarith only [gap,eq,mul_le_mul_of_nonneg_right low (sq_nonneg (m:ℤ)),show (Y:ℤ)≤ B by exact_mod_cast yB]
    refine ⟨r,by exact_mod_cast gt,?_,ok⟩
    rw [eq];unfold form;dsimp [h];ring
  obtain ⟨u,w,wp,div,high,seq⟩:=strong p Y H (d*p) (Nat.mul_pos dp prime.pos)
  have ddiv:d∣w:=(dvd_mul_right d p).trans div
  have pdiv:p∣w:=(dvd_mul_left p d).trans div
  have wz:(w:ZMod p)=0:=(ZMod.natCast_eq_zero_iff ..).mpr pdiv
  have primeAt (i:↥(shifts A)) : 0≤form A (u,w) i ∧ commonPrime p p (form A (u,w) i).toNat:=by
    obtain ⟨r,_,eq,mem⟩:=seq i
    rw [←eq,Int.toNat_natCast]
    exact ⟨Int.natCast_nonneg _,fixed_class_common _ _ mem⟩
  have base (i:↥(shifts A)) : commonPrime K K (form A (u,w) i).toNat:=by
    obtain ⟨pp,ray,clean⟩:=(common_prime_iff ..).mp (primeAt i).2
    apply (common_prime_iff ..).mpr
    exact ⟨pp,ray,fun q h odd away le => ⟨(clean q h odd away (by omega)).1,
      fun _=>(clean q h odd away (by omega)).2 (by omega)⟩⟩
  have live : patternWeight A K K (u,w)≠0:= Finset.prod_ne_zero_iff.mpr (fun i _=>by
    rw [primeWeight,ite_eq_left ⟨(primeAt i).1,base i⟩]
    exact (Real.log_pos (by exact_mod_cast (base i).1.one_lt)).ne')
  have zero: (0:ℚ)∈shifts A:=by simpa using shift_mem A 0 (by norm_num [Sun28.Ordinary.marks]: (0:ℚ)∈_)
  obtain ⟨rr,_,form0,cl0⟩:=seq ⟨0,zero⟩
  have ur:u=rr:=by simpa [form,offset] using form0.symm
  have uz:(u:ZMod p)=1:=ur ▸ fixed_norm_residue prime (by omega) (by omega) le_rfl cl0
  refine ⟨u,w,wp,ddiv,high,seq,live,?_,no_collision.mpr ?_⟩
  · simpa [obstruction,inert,inertEvent] using And.intro uz wz
  intro q hq
  obtain ⟨lo,hi,qp⟩:=Sun28.SinglePrime.mem_places.mp hq
  rintro ⟨i,j,plus,_⟩
  have rc:=(common_prime_iff ..).mp (primeAt i).2
  exact (rc.2.2 q qp (by omega) (by omega) hi).1 plus

end
end Sun28.CommonRows
#print axioms Sun28.CommonRows.fixed_norm_residue
#print axioms Sun28.CommonRows.narrow_recovered
