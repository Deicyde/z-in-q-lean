import JointSlopeHeight

namespace HeightSpecialization

private theorem gap {m n t : Nat} (nonzero : 0<n) (norm : m^2=t^2+2*n^2) :
    m≤n^2 := by
  have np := Nat.pow_pos nonzero (n:=2)
  have small : t<m := by
    apply Nat.lt_of_not_ge
    intro h
    have step:=Nat.pow_le_pow_left h 2
    omega
  cases m with
  | zero => omega
  | succ k =>
    have step:=Nat.pow_le_pow_left (show t≤k by omega) 2
    have e : (k+1)^2=k^2+2*k+1 := by grobner
    omega

private def numeratorAt (d : Nat) (q : Rat) : Int := ((d/q.den:Nat):Int)*q.num

private theorem lifted (d : Nat) (q : Rat) (dvd : q.den∣d) :
    ((numeratorAt d q:Int):Rat)=(d:Rat)*q := by
  have num:=Rat.num_divInt_den q
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at num
  have nz : (q.den:Rat)≠0 := fun h => q.den_nz (Rat.natCast_eq_zero_iff.mp h)
  have h := congrArg (fun z:Rat=>z*(q.den:Rat)) num
  have mul : (q.num:Rat)=q*(q.den:Rat) := (Rat.div_mul_cancel nz).symm.trans h
  have drep : (d:Rat)=((d/q.den:Nat):Rat)*(q.den:Rat) := by
    rw [←Rat.natCast_mul,Nat.div_mul_cancel dvd]
  simp only [numeratorAt,Rat.intCast_mul,Rat.intCast_natCast]
  rw [drep,mul]; grobner

private theorem abs_sq (z : Int) : ((z.natAbs^2:Nat):Int)=z^2 := by
  rw [← Int.natAbs_pow]
  exact Int.natAbs_of_nonneg (Int.sq_nonnneg z)

/-- A rational-square norm bounds the primitive numerator of A by the square
of the primitive numerator of B, after clearing their common denominator. -/
theorem joint_height_of_square_norm {a b t : Rat} (live : b≠0)
    (norm : a^2-2*b^2=t^2) :
    jointHeight a b ≤ (Nat.lcm a.den b.den / b.den)^2 * H (1+b^2) := by
  let d:=Nat.lcm a.den b.den
  let m:=numeratorAt d a
  let n:=numeratorAt d b
  let z:=(d:Rat)*t
  let g:=d/b.den
  have da : a.den∣d:=Nat.dvd_lcm_left .. 
  have db : b.den∣d:=Nat.dvd_lcm_right ..
  have dp : 0<d:=Nat.lcm_pos a.den_pos b.den_pos
  have md : (m:Rat)=(d:Rat)*a:=lifted d a da
  have nd : (n:Rat)=(d:Rat)*b:=lifted d b db
  have id : z^2=((m^2-2*n^2:Int):Rat) := by
    simp only [Rat.intCast_sub,Rat.intCast_mul,Rat.intCast_pow,md,nd]
    dsimp [z]; grobner
  have nums:=congrArg Rat.num id
  simp only [Rat.num_pow,Rat.num_intCast] at nums
  have eq : m.natAbs^2=z.num.natAbs^2+2*n.natAbs^2 := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_add,Int.natCast_mul,abs_sq,abs_sq,abs_sq]
    omega
  have dsplit : g*b.den=d:=Nat.div_mul_cancel db
  have gp : 0<g := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h,Nat.zero_mul] at dsplit
    omega
  have nrep : n.natAbs=g*b.num.natAbs := by
    simp only [n,numeratorAt,g,Int.natAbs_mul,Int.natAbs_natCast]
  have bp := Int.natAbs_pos.mpr (show b.num≠0 from fun h=>live (Rat.num_eq_zero.mp h))
  have npos : 0<n.natAbs := nrep ▸ Nat.mul_pos gp bp
  have mcap:=gap npos eq
  let w:=g*H b
  have dc : d≤w := dsplit ▸ Nat.mul_le_mul_left g (Nat.le_max_right ..)
  have nc : n.natAbs≤w := nrep ▸ Nat.mul_le_mul_left g (Nat.le_max_left ..)
  have wp : 1≤w:=Nat.le_trans dp dc
  have ws : w≤w^2 := by simpa only [Nat.mul_one,Nat.pow_two] using Nat.mul_le_mul_left w wp
  have mc:=Nat.le_trans mcap (Nat.pow_le_pow_left nc 2)
  have j : jointHeight a b≤w^2 := by
    have mrep : m.natAbs=d/a.den*a.num.natAbs := by
      simp only [m,numeratorAt,Int.natAbs_mul,Int.natAbs_natCast]
    change max d (max (d/a.den*a.num.natAbs) (g*b.num.natAbs))≤w^2
    rw [←mrep,←nrep]
    exact Nat.max_le.mpr ⟨Nat.le_trans dc ws,Nat.max_le.mpr ⟨mc,Nat.le_trans nc ws⟩⟩
  apply Nat.le_trans j
  change (g*H b)^2≤g^2*H (1+b^2)
  rw [Nat.mul_pow]; exact Nat.mul_le_mul_left _ (height_one_add_square b)

/-- For aligned denominators the second coefficient alone gives a linear bound. -/
theorem aligned_square_height {x y : Rat} (nz : 2*x*y≠0)
    (aligned : (x^2+2*y^2).den ∣ (2*x*y).den) :
    jointHeight (x^2+2*y^2) (2*x*y)≤H (1+(2*x*y)^2) := by
  have norm : (x^2+2*y^2)^2-2*(2*x*y)^2=(x^2-2*y^2)^2 := by grobner
  have h:=joint_height_of_square_norm nz norm
  have eq : Nat.lcm (x^2+2*y^2).den (2*x*y).den=(2*x*y).den :=
    Nat.dvd_antisymm (Nat.lcm_dvd aligned (Nat.dvd_refl _)) (Nat.dvd_lcm_right ..)
  simpa only [eq,Nat.div_self (2*x*y).den_pos,Nat.one_pow,Nat.one_mul] using h

/-- The norm-square bound requires the base and the B slope only. -/
theorem square_denominator_slope_bound {a b t l : Rat} {U : Nat}
    (live : b≠0) (norm : a^2-2*b^2=t^2) (nz : l≠0)
    (base : H l≤U) (second : H ((1+b^2)^2*l)≤U) :
    jointHeight a b ≤ (Nat.lcm a.den b.den / b.den)^2*U := by
  have z : (1+(0:Rat)^2)^2=1 := by grobner
  have h := (scale_heights (b:=0) nz base second (by simpa only [z,Rat.one_mul] using base)).1
  exact Nat.le_trans (joint_height_of_square_norm live norm) (Nat.mul_le_mul_left _ h)

#print axioms joint_height_of_square_norm
#print axioms aligned_square_height
#print axioms square_denominator_slope_bound
end HeightSpecialization
