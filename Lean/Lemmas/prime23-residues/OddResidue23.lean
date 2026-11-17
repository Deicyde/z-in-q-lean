import AnchorOrders23

namespace Prime23
open Lean.Grind PhysicalProjection.Comparison StructuralReduction
attribute [local instance] Semiring.natCast Ring.intCast

private theorem zero_of_positive {x : Rat} (pos : 0<order 3 x) : Red 3 x 0 := by
  have np : 0<natOrder 3 x.num.natAbs := by unfold order intOrder at pos; omega
  have num : 3∣x.num.natAbs := by
    apply Classical.byContradiction
    intro absent
    rw [natOrder,dif_neg (fun h=>absent h.2.2)] at np
    omega
  have den : ¬3∣x.den := fun d=>Nat.not_coprime_of_dvd_of_dvd (by decide : 2≤3) num d x.reduced
  have cast_zero (m : Int) : (m:Fin 3)=0 ↔ (3:Int)∣m :=
    (IsCharP.intCast_eq_zero_iff 3 m).trans Int.dvd_iff_emod_eq_zero.symm
  have num0:= (cast_zero _).mpr (Int.ofNat_dvd_left.mpr num)
  have denUnit : ((x.den:Int):Fin 3)≠0 :=
    fun e=>den (Int.natCast_dvd_natCast.mp ((cast_zero _).mp e))
  have canonical:=Rat.num_divInt_den x
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at canonical
  have dc : (x.den:Rat)≠0 := fun e=>x.den_nz (Rat.natCast_eq_zero_iff.mp e)
  have clr := (congrArg (fun y:Rat=>y*(x.den:Rat)) canonical.symm).trans (Rat.div_mul_cancel dc)
  refine ⟨x.num*(x.den:Int),(x.den:Int)*(x.den:Int),?_,?_,?_⟩
  · rw [Ring.intCast_mul,unit_square_3 _ denUnit]
  · rw [Ring.intCast_mul,num0,Semiring.zero_mul]
  · simp only [Rat.intCast_mul,Rat.intCast_natCast]; grobner

theorem normalized_q_zero {q : Q2} {n : Int} (h : Normalized 3 Base.qDouble q (n:Rat)) :
    PairRed 3 q (0,0) := by
  obtain ⟨u,ur,ue⟩:=h
  have seed : Base.qDouble=scale 9 (scale (1/9) Base.qDouble) := by decide +kernel
  obtain ⟨t,tr,te⟩:=normalized_output seed Base.triadic.2.1 ue ur
  have nin : Red 3 9 0 := ⟨9,1,by decide +kernel,by decide +kernel,by decide +kernel⟩
  have n2 : Red 3 ((n:Rat)^2) ((n:Fin 3)*(n:Fin 3)) := by
    rw [show (n:Rat)^2=(n:Rat)*(n:Rat) by grobner]; exact (redInt n).mul (redInt n)
  rw [te]
  simpa [scaleR,Semiring.mul_zero,Semiring.zero_mul] using tr.scale (n2.mul nin)

def principalFactor (q : Q2) := plus (1,0) (scale (-1) (times Base.D (sq q)))

theorem normalized_ordinate {q w : Q2} {n : Int} (hn : n≠0) (h : Normalized 3 Base.qDouble q (n:Rat))
    (ord : sq w=times q (principalFactor q)) : PairRed 3 w (0,0) := by
  have qr:=normalized_q_zero h
  have t: PairRed 3 (sq q) (0,0) := qr.zero_mul ⟨_,qr⟩
  have d := Base.curve_reduction.2.2.mul t
  have neg : Red 3 (-1) (-1) := redInt (-1)
  have f : PairRed 3 (principalFactor q) (1,0) := by
    apply PairRed.one_plus
    simpa [scaleR,mulR,Semiring.mul_zero,Semiring.zero_mul,AddCommMonoid.zero_add] using d.scale neg
  obtain ⟨u,ur,ue⟩:=h
  have z : Normalized 3 Base.qDouble (sq w) (n:Rat) :=
    ⟨times u (principalFactor q),ur.one_mul f,by rw [ord,ue,tm_assoc]⟩
  obtain ⟨_,_,a,b⟩:=triadic_root hn z rfl
  have nn : 0≤order 3 (n:Rat) := by
    rw [order_int (prime_of_finite (by decide) (by decide) : BinaryQuartic.Prime 3)]; omega
  exact ⟨zero_of_positive (by omega),zero_of_positive (by omega)⟩

def oneMinus (a b : Q2) := plus (1,0) (scale (-1) (times a b))
def oddChordRhs (q w : Q2) :=
  plus (times (plus (1,0) (times Base.xP q)) (plus Base.xP (scale (-1) (times Base.D q))))
    (scale (-2) (times Base.yP w))

theorem odd_chord {q w x : Q2} {n : Int} (hn : n≠0) (h : Normalized 3 Base.qDouble q (n:Rat))
    (ord : sq w=times q (principalFactor q))
    (chord : times x (sq (oneMinus Base.xP q))=oddChordRhs q w) : PairRed 3 x (0,1) := by
  have qr:=normalized_q_zero h
  have wr:=normalized_ordinate hn h ord
  have ypr : PairRed 3 Base.yP (0,0) :=
    ⟨⟨-330,16,by decide +kernel,by decide +kernel,by decide +kernel⟩,
     ⟨834,64,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩
  have neg : Red 3 (-1) (-1) := redInt (-1)
  have neg2 : Red 3 (-2) (-2) := redInt (-2)
  have den : PairRed 3 (sq (oneMinus Base.xP q)) (1,0) :=
    ((Base.curve_reduction.1.mul qr).scale neg).one_plus.one_mul
      ((Base.curve_reduction.1.mul qr).scale neg).one_plus
  have rhs : PairRed 3 (oddChordRhs q w) (0,1) :=
    ((Base.curve_reduction.1.mul qr).one_plus.mul
      (Base.curve_reduction.1.add ((Base.curve_reduction.2.2.mul qr).scale neg))).add
      ((ypr.mul wr).scale neg2)
  obtain ⟨nz,ir⟩:=den.invOne (by decide)
  have e : x=times (oddChordRhs q w) (inverse (sq (oneMinus Base.xP q))) := by
    rw [←chord,tm_assoc,inverse_clears nz,tm_one]
  exact e ▸ (rhs.mul ir)

section Field
variable {K : Type} [Field K]

theorem ordinate_identity {D x y q : K} (curve : y^2=x^3-D*x) (recip : x*q=1) :
    (y*q^2)^2=q*(1-D*q^2) := by
  calc _ = (x*q)^3*q-D*(x*q)*q^3 := by rw [show (y*q^2)^2=y^2*q^4 by grobner,curve]; grobner
       _ = _ := by rw [recip]; grobner

theorem cleared_chord {D xp yp x y q s a : K} (pCurve : yp^2=xp^3-D*xp)
    (qCurve : y^2=x^3-D*x) (recip : x*q=1) (slope : s*(x-xp)=y-yp)
    (sumX : a=s^2-x-xp) :
    a*(1-xp*q)^2=(1+xp*q)*(xp-D*q)-2*yp*(y*q^2) := by
  have sum : a*(x-xp)^2=(x+xp)*(x*xp-D)-2*yp*y := by
    calc _ = (s*(x-xp))^2-(x+xp)*(x-xp)^2 := by rw [sumX]; grobner
         _ = y^2+yp^2-2*yp*y-(x+xp)*(x-xp)^2 := by rw [slope]; grobner
         _ = _ := by rw [qCurve,pCurve]; grobner
  have ab : (x-xp)*q=1-xp*q := by grobner
  have ac : (x+xp)*q=1+xp*q := by grobner
  have ad : (x*xp-D)*q=xp-D*q := by grobner
  calc _ = a*(x-xp)^2*q^2 := by rw [←ab]; grobner
       _ = ((x+xp)*q)*((x*xp-D)*q)-2*yp*(y*q^2) := by rw [sum]; grobner
       _ = _ := by rw [ac,ad]
end Field

#print axioms normalized_ordinate
#print axioms odd_chord
#print axioms cleared_chord
end Prime23
