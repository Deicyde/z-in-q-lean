import OcticExclusion
import PhysicalSelection

namespace Sun28.ConicRemaining
open Sun28.OcticResidues Sun28.FactorHeights
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

def c {R:Type*} [CommRing R] (A B:R):R := A+7194*B
def n {R:Type*} [CommRing R] (A B:R):R := 9*B-A
def q {R:Type*} [CommRing R] (A B:R):R := 42*(-A^2+1047*A*B+64746*B^2)
def q' {R:Type*} [CommRing R] (A B:R):R := 6*n A B*c A B

private def cand : Finset ℤ:=(42:ℕ).divisors.image fun k:ℕ=>(k:ℤ)
private def live : Finset ℤ := cand.filter fun m=>
  let sqs:=squares 16
  ∃A∈sqs, ∃B∈sqs,
    ¬(ZMod.castHom (by decide:2∣16) (ZMod 2) A=0 ∧ ZMod.castHom (by decide:2∣16) (ZMod 2) B=0) ∧
    (m:ZMod 16)*c A B∈sqs ∧ q A B∈sqs ∧ q' A B∈sqs

private theorem cells : live={3} := by decide

open private signed_factor from OcticExclusion

/-- The sole rational squareclass of the quadratic factor, on every primitive input
for which the two specified integral quartics are squares. -/
theorem unique_kernel {a b U V:ℤ} (cop:a.natAbs.Coprime b.natAbs) (bn:b≠0)
    (first:q (a^2) (b^2)=U^2) (second:q' (a^2) (b^2)=V^2) :
    ∃w:ℤ, c (a^2) (b^2)=3*w^2 := by
  let C:=c (a^2) (b^2)
  let N:=n (a^2) (b^2)
  have cp:0<C:=by dsimp[C,c];nlinarith only [sq_nonneg a,sq_pos_of_ne_zero bn]
  have relation:C*(42*N)=7*V^2:=by dsimp[C,N,q'] at *;linear_combination 7*second
  obtain ⟨m,w,km,e⟩:=signed_factor cp.ne' (by decide:42≠0) (by decide) relation (by
    intro p pp hC hN
    let prime:=Nat.prime_iff_prime_int.mp pp
    rcases prime.dvd_mul.mp hN with ht|ht
    · exact_mod_cast ht
    · have det:=prime_divides_determinant pp cop (A:=1) (B:=7194) (C:=(-1)) (D:=9)
        (by simpa [C,c] using hC) (by simpa [N,n,sub_eq_add_neg,add_comm] using ht)
      have pd:p∣7203:=by exact_mod_cast (show (p:ℤ)∣7203 by simpa using det)
      exact pp.dvd_of_dvd_pow (pd.trans (by decide:7203∣42^5)))
  have mp:0 < m :=by by_contra! neg;exact cp.not_ge (e ▸ mul_nonpos_of_nonpos_of_nonneg neg (sq_nonneg w))
  have mem:m∈cand := Finset.mem_image.mpr ⟨m.natAbs,Nat.mem_divisors.mpr ⟨km,by decide⟩,by simpa using abs_of_pos mp⟩
  have sq (t:ℤ) : (t:ZMod 16)^2∈squares 16:= Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩
  have red (r:ℤ) (atp:ZMod.castHom (by decide:2∣16) (ZMod 2) ((r:ZMod 16)^2)=0) : 2∣r.natAbs:=by
    rw [map_pow,map_intCast] at atp
    simpa using Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (sq_eq_zero_iff.mp atp))
  have val:m∈live:=by
    apply Finset.mem_filter.mpr
    refine ⟨mem, (a:ZMod 16)^2,sq a,(b:ZMod 16)^2,sq b,?_,?_,?_,?_⟩
    · rintro ⟨aa,bb⟩;exact (Nat.not_coprime_of_dvd_of_dvd (by decide:1<2) (red a aa) (red b bb)) cop
    · have hsq:m*c (a^2) (b^2)=(m*w)^2:=by change m*C=_;rw [e];ring
      convert sq (m*w) using 1
      simpa [c] using congrArg (Int.castRingHom (ZMod 16)) hsq
    · convert sq U using 1
      simpa [q] using congrArg (Int.castRingHom (ZMod 16)) first
    · convert sq V using 1
      simpa [q',c,n] using congrArg (Int.castRingHom (ZMod 16)) second
  rw [cells,Finset.mem_singleton] at val
  exact ⟨w,val ▸ e⟩

end
end Sun28.ConicRemaining
#print axioms Sun28.ConicRemaining.unique_kernel
