import AlignedSeed
import ScalarKernels

/-! Remove an aligned Gaussian divisor. The quotient is a primitive
Pythagorean triple, and its norm factor divides 30 times the actual octic class. -/
namespace Sun28.PointPencils
open Sun28.WitnessHeight Sun28.ScalarQuotients
noncomputable section

structure Circle (x : ℚ) (d w : ℕ) (u v p c : ℤ) : Prop where
  positive : 0<w
  squarefree : Squarefree d
  octicSupport : d ∣ 30*(scalarClass x).natAbs
  seed : u^2+v^2=(d:ℤ)
  point : x.num=u*p-v*c ∧ (x.den:ℤ)=v*p+u*c
  primitive : IsCoprime p c
  equation : p^2+c^2=(w:ℤ)^2

private theorem kernel_dvd {d l : ℕ} {w v : ℤ} (sf : Squarefree d) (nw : w≠0)
    (same : (d:ℤ)*w^2=(l:ℤ)*v^2) : d ∣ l := by
  have square : IsSquare (((d:ℤ)*(l:ℤ):ℤ):ℚ) := by
    have e : (d:ℚ)*(w:ℚ)^2=(l:ℚ)*(v:ℚ)^2 := by exact_mod_cast same
    have nz : (w:ℚ)≠0 := by exact_mod_cast nw
    refine ⟨(l:ℚ)*v/w,?_⟩
    push_cast
    field_simp
    linear_combination (l:ℚ)*e
  have div := (Int.squarefree_natCast.mpr sf).dvd_of_isSquare_mul (Rat.isSquare_intCast_iff.mp square)
  exact_mod_cast div

/-- Every scalar slope, including zero, has an aligned integral chart. -/
theorem realized_circle (x : ℚ) :
    ∃ d w : ℕ, ∃ u v p c : ℤ, Circle x d w u v p c := by
  have bn : (x.den:ℤ)≠0:=by exact_mod_cast x.den_nz
  have primitive : IsCoprime x.num (x.den:ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr
    (by simpa only [Int.gcd_def,Int.natAbs_natCast] using x.reduced.gcd_eq_one)
  obtain ⟨d,w,_,_,_,wp,sf,norm0,_⟩:=squarefree_seed x
  have norm : x.num^2+(x.den:ℤ)^2=(d:ℤ)*(w:ℤ)^2 := by
    have nat:=congrArg (fun n:ℕ=>(n:ℤ)) norm0
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_mul,Int.natCast_natAbs,sq_abs,mul_comm] using nat
  obtain ⟨s,y,ny,twist⟩:=octic_twist x
  obtain ⟨Y,yEq⟩:=integral_point s ny twist
  obtain ⟨_,l,_,z,_,ds,_,eq⟩:=two_kernels (by simpa only [Int.natAbs_natCast] using x.reduced)
    bn s.ne_zero yEq
  have support:= (kernel_dvd sf (by exact_mod_cast wp.ne' : (w:ℤ)≠0) (norm.symm.trans eq)).trans ds
  obtain ⟨u,v,seed,⟨c,ec⟩,⟨p,ep⟩⟩:=aligned_seed x.num (x.den:ℤ) primitive d sf ⟨(w:ℤ)^2,norm⟩
  have nd : (d:ℤ)≠0 := by exact_mod_cast sf.ne_zero
  have a : x.num=u*p-v*c := by
    apply mul_left_cancel₀ nd
    linear_combination u*ep-v*ec-x.num*seed
  have b : (x.den:ℤ)=v*p+u*c := by
    apply mul_left_cancel₀ nd
    linear_combination v*ep+u*ec-(x.den:ℤ)*seed
  have pc : IsCoprime p c := by
    obtain ⟨s,t,bez⟩:=primitive
    refine ⟨s*u+t*v,-s*v+t*u,?_⟩
    rw [a,b] at bez
    linear_combination bez
  have py : p^2+c^2=(w:ℤ)^2:=by
    apply mul_left_cancel₀ nd
    rw [a,b] at norm
    linear_combination norm-(p^2+c^2)*seed
  exact ⟨d,w,u,v,p,c,⟨wp,sf,support,seed,⟨a,b⟩,pc,py⟩⟩

end
end Sun28.PointPencils
#print axioms Sun28.PointPencils.realized_circle
