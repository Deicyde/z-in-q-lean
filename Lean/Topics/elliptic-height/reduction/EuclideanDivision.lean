import QuadraticNumerator
import QuadraticPivots

namespace EllipticHeight.Reduction
open QuadraticInt

/-- The balanced integer quotient for either sign of the denominator. -/
def nearest (p d : Int) : Int :=
  if d<0 then -(p.bdiv d.natAbs) else p.bdiv d.natAbs

private theorem nearest_identity (p d : Int) :
    d*nearest p d+p.bmod d.natAbs=p := by
  have h:=Int.bdiv_add_bmod p d.natAbs
  unfold nearest
  split
  next s =>
    rw [Int.ofNat_natAbs_of_nonpos (Int.le_of_lt s)] at h
    grobner
  next s =>
    rw [Int.natAbs_of_nonneg (by omega : 0≤d)] at h
    exact h

private theorem residue_square (p : Int) (m : Nat) (hm : 0<m) :
    4*(p.bmod m)^2≤(m:Int)^2 := by
  have lo:=Int.le_bmod (x:=p) hm
  have hi:=Int.bmod_lt (x:=p) hm
  have hl : 0≤(m:Int)+2*p.bmod m := by omega
  have hr : 0≤(m:Int)-2*p.bmod m := by omega
  have h:=Int.mul_nonneg hl hr
  have eq : ((m:Int)+2*p.bmod m)*((m:Int)-2*p.bmod m)=(m:Int)^2-4*(p.bmod m)^2 := by grobner
  omega

theorem norm_nonzero {y : R} (nz : y≠(0,0)) : norm y≠0 := by
  intro h
  have lift:=congrArg (fun k : Int=>(k:Rat)) h
  have eq : CircuitTransport.Quadratic.norm (y.1:Rat) (y.2:Rat)=0 := by
    simpa only [norm,CircuitTransport.Quadratic.norm,Rat.intCast_sub,Rat.intCast_pow,
      Rat.intCast_mul] using lift
  obtain ⟨a,b⟩:=(CircuitTransport.Quadratic.norm_zero_iff ..).mp eq
  exact nz (Prod.ext (Rat.intCast_inj.mp a) (Rat.intCast_inj.mp b))

def minus (a b : R) : R := (a.1-b.1,a.2-b.2)

/-- Round both coefficients of x/y after multiplying by the conjugate of y. -/
def quotient (x y : R) : R :=
  let p:=mul x (conj y)
  (nearest p.1 (norm y),nearest p.2 (norm y))

def remainder (x y : R) : R := minus x (mul y (quotient x y))

theorem division_identity (x y : R) : x=plus (mul y (quotient x y)) (remainder x y) := by
  apply Prod.ext <;> dsimp [remainder,minus,plus] <;> omega

private theorem residue_identity (x y : R) :
    let e:=mul x (conj y)
    let m:=(norm y).natAbs
    mul (remainder x y) (conj y)=(e.1.bmod m,e.2.bmod m) := by
  dsimp only
  let e:=mul x (conj y)
  have elim (q : R) :
      mul (minus x (mul y q)) (conj y)=minus e (mul (norm y,0) q) := by
    apply Prod.ext <;> dsimp [minus,mul,e,conj,norm] <;> grobner
  rw [remainder,elim]
  have a:=nearest_identity e.1 (norm y)
  have b:=nearest_identity e.2 (norm y)
  apply Prod.ext
  · change e.1-(norm y*nearest e.1 (norm y)+2*0*nearest e.2 (norm y))=e.1.bmod (norm y).natAbs
    omega
  · change e.2-(norm y*nearest e.2 (norm y)+0*nearest e.1 (norm y))=e.2.bmod (norm y).natAbs
    omega

/-- At every division step the absolute norm of the remainder is at most
one half the absolute norm of the divisor. -/
theorem half_norm (x y : R) (nz : y≠(0,0)) :
    2*(norm (remainder x y)).natAbs≤(norm y).natAbs := by
  let m:=(norm y).natAbs
  let e:=mul x (conj y)
  let u:=e.1.bmod m
  let v:=e.2.bmod m
  have pos : 0<m := Int.natAbs_pos.mpr (norm_nonzero nz)
  have p : 4*u^2≤(m:Int)^2 := residue_square _ _ pos
  have q : 4*v^2≤(m:Int)^2 := residue_square _ _ pos
  have h : 2*((u^2-2*v^2).natAbs:Int)≤(m:Int)^2 := by
    have un:=Int.sq_nonnneg u
    have vn:=Int.sq_nonnneg v
    rcases Int.natAbs_eq (u^2-2*v^2) with z|z <;> omega
  have bound : 2*(u^2-2*v^2).natAbs≤m*m := by
    apply Int.ofNat_le.mp
    simpa only [Int.natCast_mul,Int.pow_succ,Int.pow_zero,Int.one_mul] using h
  have conj_norm : norm (conj y)=norm y := by dsimp [norm,conj]; grobner
  have ident:=congrArg norm (residue_identity x y)
  rw [mul_norm,conj_norm] at ident
  change norm (remainder x y)*norm y=u^2-2*v^2 at ident
  have natIdent:=congrArg Int.natAbs ident
  rw [Int.natAbs_mul] at natIdent
  apply Nat.le_of_mul_le_mul_right (c:=m) _ pos
  rw [Nat.mul_assoc]
  exact (natIdent ▸ bound : 2*((norm (remainder x y)).natAbs*m)≤m*m)

theorem strict_descent (x y : R) (nz : y≠(0,0)) :
    (norm (remainder x y)).natAbs<(norm y).natAbs := by
  have h:=half_norm x y nz
  have p:=Int.natAbs_pos.mpr (norm_nonzero nz)
  omega

/-- Both signs of the divisor norm attain the factor one half. -/
theorem sharp_examples :
    remainder (0,1) (2,0)=(0,-1) ∧ 2*(norm (0,-1)).natAbs=(norm (2,0)).natAbs ∧
    remainder (1,0) (0,1)=(1,0) ∧ 2*(norm (1,0)).natAbs=(norm (0,1)).natAbs := by decide

#print axioms division_identity
#print axioms half_norm
#print axioms strict_descent
#print axioms sharp_examples
end EllipticHeight.Reduction
