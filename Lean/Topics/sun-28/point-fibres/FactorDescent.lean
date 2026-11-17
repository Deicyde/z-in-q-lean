import PrescribedNorm

namespace Sun28.PointFibres
open Sun28.PointDescent ZInQ.RouteK
noncomputable section

def smallFactor (b : ℕ) (x y : ℤ) : ℤ := x^2-(b:ℤ)*y^2
def largeFactor (b : ℕ) (x y : ℤ) : ℤ := x^2-81*(b:ℤ)*y^2

theorem common_prime {b : ℕ} {x y : ℤ} (primitive : x.natAbs.Coprime y.natAbs)
    {p : ℕ} (pp : p.Prime) (h : (p:ℤ)∣smallFactor b x y) (j : (p:ℤ)∣largeFactor b x y) :
    p∣10*b := by
  let pi := (p:ℤ)
  have ip : Prime pi:=Nat.prime_iff_prime_int.mp pp
  have sf : pi∣x^2-(b:ℤ)*y^2:=h
  have df : pi∣80*(b:ℤ)*y^2:=by
    convert dvd_sub h j using 1
    unfold smallFactor largeFactor;ring
  rcases ip.dvd_mul.mp df with cb|yy
  · have nb : p∣80*b:=by change (p:ℤ)∣80*(b:ℤ) at cb;exact_mod_cast cb
    have e : 80*b=2^3*(10*b) := by ring
    rw [e] at nb
    rcases pp.dvd_mul.mp nb with pt|out
    · have pt2 : p∣2:=pp.dvd_of_dvd_pow pt
      have eq:=(Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).mp pt2
      exact eq ▸ dvd_mul_of_dvd_left (by decide : 2∣10) b
    · exact out
  · have py : pi∣y:=ip.dvd_of_dvd_pow yy
    have xx : pi∣x^2:=by
      convert dvd_add sf (dvd_mul_of_dvd_right yy (b:ℤ)) using 1
      ring
    have px : pi∣x:=ip.dvd_of_dvd_pow xx
    exact False.elim ((Nat.not_coprime_of_dvd_of_dvd pp.one_lt
      (by simpa [pi] using Int.natAbs_dvd_natAbs.mpr px)
      (by simpa [pi] using Int.natAbs_dvd_natAbs.mpr py)) primitive)

/-- Removing the common radical of the two signed factors partitions the prescribed class. -/
theorem integer_partition {b θ : ℕ} {x y : ℤ} {w : ℚ} (bp : 0<b) (sf : Squarefree θ)
    (primitive : x.natAbs.Coprime y.natAbs) (wn : w≠0)
    (E : (θ:ℚ)*w^2=(smallFactor b x y:ℚ)*(largeFactor b x y:ℚ)) :
    ∃ (d f g : ℕ) (a c : ℕ), d∣10*b ∧ Squarefree d ∧ f.Coprime g ∧ θ=f*g ∧
      0<a ∧ 0<c ∧ (smallFactor b x y).natAbs=d*f*a^2 ∧ (largeFactor b x y).natAbs=d*g*c^2 := by
  have pos : (0:ℚ)<θ:=by exact_mod_cast Nat.pos_of_ne_zero sf.ne_zero
  have prodpos : 0<(smallFactor b x y:ℚ)*(largeFactor b x y:ℚ):=E ▸ mul_pos pos (sq_pos_of_ne_zero wn)
  have IZ : 0<smallFactor b x y*largeFactor b x y:=by exact_mod_cast prodpos
  let X := (smallFactor b x y).natAbs
  let Y := (largeFactor b x y).natAbs
  have xn : X≠0:=Int.natAbs_ne_zero.mpr (left_ne_zero_of_mul IZ.ne')
  have yn : Y≠0:=Int.natAbs_ne_zero.mpr (right_ne_zero_of_mul IZ.ne')
  have xk := sqfNat_squarefree X
  have yk := sqfNat_squarefree Y
  obtain ⟨a,an,A⟩:=sqfNat_mul_sq xn
  obtain ⟨c,cn,C⟩:=sqfNat_mul_sq yn
  let d := Nat.gcd (sqfNat X) (sqfNat Y)
  obtain ⟨f,g,fg,fx,gy⟩:=Nat.exists_coprime (sqfNat X) (sqfNat Y)
  change sqfNat X=f*d at fx
  change sqfNat Y=g*d at gy
  have dX : d∣sqfNat X:=Nat.gcd_dvd_left .. 
  have dY : d∣sqfNat Y:=Nat.gcd_dvd_right ..
  have ds:=xk.squarefree_of_dvd dX
  have fs:=xk.squarefree_of_dvd (show f∣sqfNat X by rw [fx];exact dvd_mul_right ..)
  have gs:=yk.squarefree_of_dvd (show g∣sqfNat Y by rw [gy];exact dvd_mul_right ..)
  have X' : X=d*f*a^2:=by rw [A,fx];ring
  have Y' : Y=d*g*c^2:=by rw [C,gy];ring
  have dnum (p : ℕ) (pp:p.Prime) (he:p∣d) : p∣10*b:=by
    have px : p∣X:=he.trans (dX.trans ⟨a^2,A⟩)
    have py : p∣Y:=he.trans (dY.trans ⟨c^2,C⟩)
    apply common_prime primitive pp
    · exact Int.natAbs_dvd_natAbs.mp (by simpa using px)
    · exact Int.natAbs_dvd_natAbs.mp (by simpa using py)
  have n10 : 10*b≠0:=mul_ne_zero (by decide) bp.ne'
  have charge : d∣10*b:=by
    rw [← Nat.prod_primeFactors_of_squarefree ds,Nat.prod_primeFactors_dvd_iff n10]
    intro p hp
    have pp:=Nat.prime_of_mem_primeFactors hp
    exact Nat.mem_primeFactors.mpr ⟨pp,dnum p pp (Nat.dvd_of_mem_primeFactors hp),n10⟩
  have XX : (X*Y:ℕ)=(smallFactor b x y*largeFactor b x y).natAbs:=by
    dsimp [X,Y];rw [Int.natAbs_mul]
  have eq : (θ:ℚ)*w^2=(X:ℚ)*Y:=by
    rw [E,←Nat.cast_mul,XX,←Int.cast_natCast,Int.natAbs_of_nonneg IZ.le,Int.cast_mul]
  have nz : (d*a*c:ℕ)≠0:=mul_ne_zero (mul_ne_zero ds.ne_zero an) cn
  have s1:=sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr sf) wn
    (show (θ:ℚ)*w^2=(θ:ℤ)*(w:ℚ)^2 by norm_cast)
  have s2:=sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr ((Nat.squarefree_mul fg).mpr ⟨fs,gs⟩))
    (show ((d*a*c:ℕ):ℚ)≠0 by exact_mod_cast nz)
    (show (θ:ℚ)*w^2=((f*g:ℕ):ℤ)*((d*a*c:ℕ):ℚ)^2 by rw [eq,X',Y'];push_cast;ring)
  exact ⟨d,f,g,a,c,charge,ds,fg,by exact_mod_cast s1.symm.trans s2,
    Nat.pos_of_ne_zero an,Nat.pos_of_ne_zero cn,X',Y'⟩

/-- At a rational quartic point use the reduced numerator and denominator of its nonzero k. -/
theorem partition_of_auxiliary {b θ : ℕ} (bp : 0<b) (sf : Squarefree θ)
    (cov : AuxiliaryCover (b:ℚ) (θ:ℚ)) :
    ∃ (x y : ℤ) (d f g a c : ℕ), x≠0 ∧ y≠0 ∧ x.natAbs.Coprime y.natAbs ∧
      d∣10*b ∧ Squarefree d ∧ f.Coprime g ∧ θ=f*g ∧ 0<a ∧ 0<c ∧
      (smallFactor b x y).natAbs=d*f*a^2 ∧ (largeFactor b x y).natAbs=d*g*c^2 ∧
      0<smallFactor b x y*largeFactor b x y := by
  obtain ⟨k,w,kn,wn,eq⟩:=cov
  let x:=k.num
  let y:ℤ:=k.den
  have cop:x.natAbs.Coprime y.natAbs:=by simpa [x,y] using k.reduced
  have yq : (y:ℚ)≠0:=by dsimp [y];exact_mod_cast k.den_ne_zero
  have xn : x≠0:=Rat.num_ne_zero.mpr kn
  have kx : (x:ℚ)=k*y:=(div_eq_iff yq).mp (Rat.num_div_den k)
  have Eq : (θ:ℚ)*(w*y^2)^2=(smallFactor b x y:ℚ)*(largeFactor b x y:ℚ):=by
    unfold smallFactor largeFactor;push_cast;rw [kx];linear_combination (y:ℚ)^4*eq
  have wn' : w*(y:ℚ)^2≠0 :=mul_ne_zero wn (pow_ne_zero _ yq)
  obtain ⟨d,f,g,a,c,H⟩:=integer_partition bp sf cop wn' Eq
  refine ⟨x,y,d,f,g,a,c,xn,by exact_mod_cast yq,cop,H.1,H.2.1,H.2.2.1,H.2.2.2.1,
    H.2.2.2.2.1,H.2.2.2.2.2.1,H.2.2.2.2.2.2.1,H.2.2.2.2.2.2.2,?_⟩
  have tp : (0:ℚ)<θ:=by exact_mod_cast Nat.pos_of_ne_zero sf.ne_zero
  have epos:=(Eq ▸ mul_pos tp (sq_pos_of_ne_zero wn') :
    0<(smallFactor b x y:ℚ)*(largeFactor b x y:ℚ))
  exact_mod_cast epos
end
end Sun28.PointFibres
#print axioms Sun28.PointFibres.common_prime
#print axioms Sun28.PointFibres.integer_partition
#print axioms Sun28.PointFibres.partition_of_auxiliary
