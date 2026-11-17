import ScalarContacts

namespace StructuralHeights
open IndependentIndices Lean.Grind InputRestriction

def rawSextic {R : Type} [CommRing R] (m n : R) : R :=
  let u := 119*m^2-91*n^2
  let v := n^2
  (u^2+2401*v^2)*(u^2+2400*v^2)*(32*u^2+77175*v^2)

theorem raw_scale (x : Rat) :
    let t:=SquareGate.shift x
    let z:=SquareGate.value x
    ∃ g : Nat, g≠0 ∧ rawSextic t.num (t.den:Int) = (g:Int)^6*sextic z.num z.den := by
  let t:=SquareGate.shift x
  let z:=SquareGate.value x
  change ∃ g : Nat, g≠0 ∧ rawSextic t.num (t.den:Int)= (g:Int)^6*sextic z.num z.den
  let a := 119*t.num^2-91*(t.den:Int)^2
  have eq : mkRat a (t.den^2) = z := by
    calc
      _ = mkRat z.num z.den := by
        apply (Rat.mkRat_eq_iff (by simp [t.den_nz]) z.den_nz).mpr
        have h := physical_cross x
        change (z.num+91*(z.den:Int))*(t.den:Int)^2=119*(z.den:Int)*t.num^2 at h
        rw [Int.natCast_pow]
        dsimp [a]
        grobner
      _ = _ := Rat.mkRat_self z
  obtain ⟨g,ng,num,den⟩ := Rat.mkRat_num_den (by simp [t.den_nz]) eq
  change a=z.num*(g:Int) at num
  change t.den^2=z.den*g at den
  have denInt := congrArg (fun j : Nat=>(j:Int)) den
  simp only [Int.natCast_mul,Int.natCast_pow] at denInt
  refine ⟨g,ng,?_⟩
  change (a^2+2401*((t.den:Int)^2)^2)*(a^2+2400*((t.den:Int)^2)^2)*
    (32*a^2+77175*((t.den:Int)^2)^2) = _
  rw [num,denInt]
  unfold sextic firstForm secondForm thirdForm
  grobner

attribute [local instance] Semiring.natCast Ring.intCast

private theorem residue {p : Nat} [NeZero p] (a : Int) :
    (a:Fin p)=0 ↔ (p:Int)∣a := (IsCharP.intCast_eq_zero_iff p a).trans Int.dvd_iff_emod_eq_zero.symm

private theorem raw_cast {p : Nat} [NeZero p] (m n : Int) :
    ((rawSextic m n:Int):Fin p) = rawSextic (m:Fin p) (n:Fin p) := by
  unfold rawSextic
  simp only [Ring.intCast_add,Ring.intCast_mul,Ring.intCast_pow,Ring.intCast_sub]
  rfl

private theorem at_least_one_unit {p : Nat} (hp : Prime p) (r : Rat) :
    ¬(p:Int)∣r.num ∨ ¬(p:Int)∣(r.den:Int) := by
  by_cases h : (p:Int)∣r.num
  · right
    intro k
    have div := (Int.gcd_eq_one_iff.mp (coordinates_primitive r)) _ h k
    have := Nat.le_of_dvd (by decide : 0<1) (Int.ofNat_dvd_left.mp div)
    have := hp.1
    omega
  · exact Or.inl h

private theorem table3 : ∀ m n : Fin 3, m≠0 ∨ n≠0 → rawSextic m n≠0 := by decide

theorem unit_at_3 (x : Rat) :
    let z:=SquareGate.value x
    ¬(3:Int)∣sextic z.num z.den := by
  let t:=SquareGate.shift x
  obtain ⟨g,_,eq⟩:=raw_scale x
  have primitive : (t.num:Fin 3)≠0 ∨ ((t.den:Int):Fin 3)≠0 :=
    (at_least_one_unit prime3 t).imp (fun h e=>h ((residue _).mp e)) (fun h e=>h ((residue _).mp e))
  dsimp only
  intro d
  have div := (residue (p:=3) _).mpr (show (3:Int)∣rawSextic t.num (t.den:Int) from
    eq ▸ Int.dvd_mul_of_dvd_right d)
  exact table3 _ _ primitive (by rw [←raw_cast (p:=3)];exact div)

private theorem prime2 : Prime 2 := by
  refine ⟨by decide,fun d h=>?_⟩
  have le := Nat.le_of_dvd (by decide : 0<2) h
  have z : d≠0 := by rintro rfl;contradiction
  omega

private def bad64 (v : Fin 64) : Bool := [10,18,32,42,48,50].contains v

private theorem chart64 : (∀ t : Fin 64, bad64 (35*rawSextic t 1)=true) ∧
    (∀ t : Fin 64, bad64 (35*rawSextic 1 t)=true) := by decide

private theorem squares64 : ∀ a : Fin 64, bad64 (a^2)=false := by decide

private theorem inverse64 : ∀ a : Fin 64, 32*a≠0 → a^15*a=1 := by decide

private theorem homogeneous {R : Type} [CommRing R] (m n c : R) :
    rawSextic (c*m) (c*n)=c^12*rawSextic m n := by
  have w : 119*(c*m)^2-91*(c*n)^2=c^2*(119*m^2-91*n^2) := by grobner
  have v : (c*n)^2=c^2*n^2 := by grobner
  unfold rawSextic
  rw [w,v]
  generalize 119*m^2-91*n^2=u
  generalize n^2=t
  grobner

private theorem nonsquare64 (m n a : Fin 64) (primitive : 32*m≠0 ∨ 32*n≠0) :
    35*rawSextic m n≠a^2 := by
  intro e
  have scaled (c : Fin 64) : 35*rawSextic (c*m) (c*n)=(c^6*a)^2 := by
    rw [homogeneous]
    calc
      _ = c^12*(35*rawSextic m n) := by grobner
      _ = _ := by rw [e];grobner
  rcases primitive with odd|odd
  · have h:=scaled (m^15)
    rw [inverse64 _ odd] at h
    have impossible:=chart64.2 (m^15*n)
    rw [h,squares64] at impossible
    contradiction
  · have h:=scaled (n^15)
    rw [inverse64 _ odd] at h
    have impossible:=chart64.1 (n^15*m)
    rw [h,squares64] at impossible
    contradiction

private theorem odd64 (z : Int) (h : ¬(2:Int)∣z) : 32*(z:Fin 64)≠0 := by
  intro zero
  have ze : (((32:Int)*z:Int):Fin 64)=0 := by simpa only [Ring.intCast_mul] using zero
  have d := (residue _).mp ze
  have two : ((32:Int)*2)∣32*z := d
  exact h (Int.dvd_of_mul_dvd_mul_left (by decide : (32:Int)≠0) two)

theorem no_twist_35 (x : Rat) (s : Int) :
    let z:=SquareGate.value x
    sextic z.num z.den ≠ 35*s^2 := by
  let t:=SquareGate.shift x
  obtain ⟨g,_,eq⟩ := raw_scale x
  have prim := (at_least_one_unit prime2 t).imp (odd64 _) (odd64 _)
  dsimp only
  intro h
  have es : (35:Int)*rawSextic t.num (t.den:Int)=(35*(g:Int)^3*s)^2 := by rw [eq,h];grobner
  have rf:=congrArg (fun k : Int=>(k:Fin 64)) es
  simp only [Ring.intCast_mul,Ring.intCast_pow,raw_cast] at rf
  exact nonsquare64 _ _ _ prim rf

def EmptyScalar (x : Rat) := ∀ p, Prime p → ¬(p:Int)∣210 → ¬Contact p (coordinates (SquareGate.label x))

private theorem positive_form (u : Int) (v : Nat) (hv : v≠0) : 0<sextic u v := by
  have sq : 0≤u^2 := Int.pow_nonneg_of_even (by decide)
  have vp : 0<(v:Int)^2 := Int.pow_pos (by omega)
  unfold sextic firstForm secondForm thirdForm
  exact Int.mul_pos (Int.mul_pos (by omega) (by omega)) (by omega)

private theorem bound70 (x : Rat) (empty : EmptyScalar x) (d : Nat) (dp : 0<d)
    (sf : Squarefree d) (support : ∀ p, Prime p → (OddOrder p (sextic (SquareGate.value x).num (SquareGate.value x).den) ↔ p∣d)) :
    d∣70 := by
  apply squarefree_dvd_of_support _ _ dp sf
  intro p hp pd
  have odd := (support p hp).mpr pd
  have bad : (p:Int)∣210 := by
    apply Classical.byContradiction
    intro good
    exact empty p hp good ((physical_contact hp good x).mpr odd)
  have prod : (p:Int)∣3*70 := bad
  rcases (prime_dvd_mul hp).mp prod with three|rest
  · have t := prime3.2 p (Int.ofNat_dvd.mp three)
    have hbig:=hp.1
    have ep : p=3 := by omega
    subst p
    exact False.elim ((unit_at_3 x) (odd_dvd odd))
  · exact Int.ofNat_dvd.mp rest

private theorem square_character : ∀ d s a : Fin 17, d*s^2=a^2 → a≠0 → d^8=1 := by decide

private theorem possible : ∀ d : Fin 71, d.val∣70 → ((d.val:Fin 17)^8=1) →
    d.val=1 ∨ d.val=2 ∨ d.val=35 ∨ d.val=70 := by decide

/-- Every input with an empty scalar contact set would lie on one of three explicit twists. -/
theorem empty_twists (x : Rat) (empty : EmptyScalar x) :
    let z:=SquareGate.value x
    ∃ d s : Nat, (d=1 ∨ d=2 ∨ d=70) ∧ sextic z.num z.den=(d:Int)*(s:Int)^2 := by
  let z:=SquareGate.value x
  let f:=sextic z.num z.den
  have pos : 0<f := positive_form z.num z.den z.den_nz
  obtain ⟨d,s,sf,sp,eq,support⟩ := kernel_support f.natAbs (Int.natAbs_pos.mpr (Int.ne_of_gt pos))
  have fi : (f.natAbs:Int)=f := Int.natAbs_of_nonneg (Int.le_of_lt pos)
  rw [fi] at support
  have dp : 0<d := by
    by_cases h : d=0
    · simp [h] at eq;omega
    · omega
  have div := bound70 x empty d dp sf support
  have ef := congrArg (fun n : Nat=>(n:Int)) eq
  change (f.natAbs:Int)=((d*s^2:Nat):Int) at ef
  rw [fi,Int.natCast_mul,Int.natCast_pow] at ef
  obtain ⟨unit,a,sqa⟩ := square_at_17 x
  change (f:Fin 17)=a^2 at sqa
  have nz : a≠0 := by
    intro az
    rw [az] at sqa
    exact unit ((residue _).mp (by simpa using sqa))
  have finite := congrArg (fun i : Int=>(i:Fin 17)) ef
  simp only [Ring.intCast_mul,Ring.intCast_pow,Ring.intCast_natCast] at finite
  have ch := square_character _ _ _ (finite.symm.trans sqa) nz
  have le:=Nat.le_of_dvd (by decide : 0<70) div
  rcases possible ⟨d,by omega⟩ div ch with dd|dd|dd|dd
  · exact ⟨d,s,Or.inl dd,ef⟩
  · exact ⟨d,s,Or.inr (Or.inl dd),ef⟩
  · change d=35 at dd
    subst d
    exact False.elim (no_twist_35 x (s:Int) ef)
  · exact ⟨d,s,Or.inr (Or.inr dd),ef⟩

/-- The curve coordinates X,Y,Z give the affine rational point (X/Z²,Y/Z³). -/
theorem empty_elliptic (x : Rat) (empty : EmptyScalar x) :
    ∃ d : Nat, (d=1 ∨ d=2 ∨ d=70) ∧ ∃ X Y Z : Int,
      0<Z ∧ 32*(d:Int)*Z^2<X ∧ Y^2=X*(X-32*(d:Int)*Z^2)*(X+343*(d:Int)*Z^2) := by
  let z:=SquareGate.value x
  obtain ⟨d,s,hd,ef⟩:=empty_twists x empty
  change sextic z.num z.den = (d:Int)*(s:Int)^2 at ef
  let X:=32*(d:Int)*firstForm z.num z.den
  refine ⟨d,hd,X,32*(d:Int)^2*(s:Int),(z.den:Int),by have := z.den_nz;omega,?_,?_⟩
  · have dp : 0<(d:Int) := by rcases hd with h|h|h <;> omega
    apply Int.mul_lt_mul_of_pos_left _ (Int.mul_pos (by decide) dp)
    have n2 : 0<(z.den:Int)^2 := Int.pow_pos (by have :=z.den_nz;omega)
    have u2 : 0≤z.num^2 := Int.pow_nonneg_of_even (by decide)
    unfold firstForm;omega
  · change _=32*(d:Int)*firstForm z.num z.den*(_-32*(d:Int)*(z.den:Int)^2)*(_+343*(d:Int)*(z.den:Int)^2)
    dsimp [X]
    have equivalence (u v D S : Int) (e : sextic u v=D*S^2) :
        (32*D^2*S)^2=(32*D*firstForm u v)*(32*D*firstForm u v-32*D*v^2)*
          (32*D*firstForm u v+343*D*v^2) := by
      calc
        _=(32:Int)^2*D^3*(D*S^2) := by grobner
        _=_ := by rw [←e];unfold sextic firstForm secondForm thirdForm;grobner
    exact equivalence _ _ _ _ ef

#print axioms raw_scale
#print axioms unit_at_3
#print axioms no_twist_35
#print axioms empty_twists
#print axioms empty_elliptic
end StructuralHeights
