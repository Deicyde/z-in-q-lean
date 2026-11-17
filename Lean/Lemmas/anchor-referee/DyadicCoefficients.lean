import SexticOrder
import ComparisonChart

namespace AnchorCollision.Dyadic
open StructuralReduction BinaryQuartic PhysicalProjection.Comparison

private theorem twoPrime : Prime 2 := prime_of_finite (by decide) (by decide)
private abbrev v := primeOrder 2 twoPrime

private theorem square_order {a : Rat} (ha : a≠0) :
    a^2≠0 ∧ order 2 (a^2)=2*order 2 a := power_order v ha 2

private theorem other_order {b : Rat} (hb : b≠0) :
    -(2*b^2)≠0 ∧ order 2 (-(2*b^2))=1+2*order 2 b := by
  obtain ⟨live,eq⟩:=square_order hb
  have mul_live : (2:Rat)*b^2≠0 := by grind [Rat.mul_eq_zero]
  refine ⟨by grind,?_⟩
  calc order 2 (-(2*b^2))=order 2 (2*b^2) := v.neg _ mul_live
       _ = order 2 2 + order 2 (b^2) := v.mul _ _ (by decide) live
       _ = _ := by rw [show order 2 2=1 from order_prime twoPrime,eq]

private theorem real_only (a : Rat) : norm (a,0)=a^2 := by dsimp [norm]; grobner
private theorem imag_only (b : Rat) : norm (0,b)=-(2*b^2) := by dsimp [norm]; grobner

/-- Both summands of the quadratic norm have finite orders of opposite parity. -/
theorem norm_min {a b : Rat} (ha : a≠0) (hb : b≠0) :
    order 2 (norm (a,b))=min (2*order 2 a) (1+2*order 2 b) := by
  obtain ⟨sa,oa⟩:=square_order ha
  obtain ⟨sb,ob⟩:=other_order hb
  have ne : order 2 (a^2)≠order 2 (-(2*b^2)) := by omega
  change order 2 (a^2-2*b^2)=_
  rw [Rat.sub_eq_add_neg]
  exact (v.addUnequal _ _ sa sb ne).2.trans (by change min (order 2 _) (order 2 _)=_; rw [oa,ob])

/-- For nonzero z in Q(√2), an even norm order is twice the order of its
rational coordinate. The coefficient of √2 may vanish. -/
theorem real_of_even {z : Q2} (live : z≠(0,0))
    (even : ∃ k : Int, order 2 (norm z)=2*k) :
    z.1≠0 ∧ order 2 (norm z)=2*order 2 z.1 := by
  obtain ⟨a,b⟩:=z
  obtain ⟨k,hk⟩:=even
  by_cases ha : a=0
  · subst a
    have hb : b≠0 := fun e=>live (by rw [e])
    rw [imag_only,(other_order hb).2] at hk
    omega
  refine ⟨ha,?_⟩
  by_cases hb : b=0
  · subst b
    rw [real_only,(square_order ha).2]
  · rw [norm_min ha hb] at hk ⊢
    change min (2*order 2 a) (1+2*order 2 b)=2*order 2 a
    omega

private theorem order_zero : order 2 0=0 := by decide +kernel

/-- A 2-integral norm has two 2-integral coordinates, including at zero. -/
theorem integral_coordinates {z : Q2} (h : 0≤order 2 (norm z)) :
    0≤order 2 z.1 ∧ 0≤order 2 z.2 := by
  obtain ⟨a,b⟩:=z
  change 0≤order 2 a ∧ 0≤order 2 b
  by_cases ha : a=0
  · subst a
    rw [order_zero]
    by_cases hb : b=0
    · rw [hb,order_zero]; decide
    · rw [imag_only,(other_order hb).2] at h
      omega
  by_cases hb : b=0
  · subst b
    rw [real_only,(square_order ha).2] at h
    rw [order_zero]; omega
  · rw [norm_min ha hb] at h
    omega

/-- Reduced rational denominators give the same dyadic integrality test. -/
theorem integral_iff_odd_den (x : Rat) : 0≤order 2 x ↔ ¬2∣x.den := by
  constructor
  · intro nonneg present
    have unit : ¬(2:Int)∣x.num :=
      fun d=>Nat.not_coprime_of_dvd_of_dvd (by decide : 2≤2)
        (Int.ofNat_dvd_left.mp d) present x.reduced
    have num := order_int_unit twoPrime unit
    rw [order_int twoPrime] at num
    have den : 0<natOrder 2 x.den := by
      rw [natOrder,dif_pos ⟨by decide,x.den_pos,present⟩]; omega
    unfold order at nonneg
    omega
  · intro absent
    have den : natOrder 2 x.den=0 := by rw [natOrder,dif_neg (fun h=>absent h.2.2)]
    unfold order
    rw [den]; omega

theorem odd_den_coordinates {z : Q2} (h : ¬2∣(norm z).den) :
    (¬2∣z.1.den) ∧ (¬2∣z.2.den) := by
  obtain ⟨a,b⟩:=integral_coordinates ((integral_iff_odd_den _).mpr h)
  exact ⟨(integral_iff_odd_den _).mp a,(integral_iff_odd_den _).mp b⟩

/-- Rational coordinate of the product of four nonzero signed abscissas.
The factors enter only through the four dyadic orders of their rational norms. -/
theorem four_abscissas {a b c d : Q2} {i j k l : Int}
    (ha : norm a≠0) (hb : norm b≠0) (hc : norm c≠0) (hd : norm d≠0)
    (oa : order 2 (norm a)= -6-4*i) (ob : order 2 (norm b)= -6-4*j)
    (oc : order 2 (norm c)= -6-4*k) (od : order 2 (norm d)= -6-4*l) :
    let C:= (times (times (times a b) c) d).1
    C≠0 ∧ order 2 (4096*C)= -2*(i+j+k+l) := by
  let t:=times (times (times a b) c) d
  have factor : norm t=norm a*norm b*norm c*norm d := by
    dsimp only [t]; rw [norm_product,norm_product,norm_product]
  have hab : norm a*norm b≠0 := by grind [Rat.mul_eq_zero]
  have habc : norm a*norm b*norm c≠0 := by grind [Rat.mul_eq_zero]
  have nz : norm t≠0 := by rw [factor]; grind [Rat.mul_eq_zero]
  have live : t≠(0,0) := fun e=>nz (by rw [e,real_only]; decide)
  have total : order 2 (norm t)= -24-4*(i+j+k+l) := by
    rw [factor]
    change v.ord _=_
    rw [v.mul _ _ habc hd,v.mul _ _ hab hc,v.mul _ _ ha hb]
    change order 2 (norm a)+order 2 (norm b)+order 2 (norm c)+order 2 (norm d)=_
    omega
  obtain ⟨r,ord⟩:=real_of_even live ⟨-12-2*(i+j+k+l),by omega⟩
  refine ⟨r,?_⟩
  change order 2 (4096*t.1)=_
  have scale : order 2 4096=12 := by
    rw [show (4096:Rat)=(2:Rat)^12 by decide]
    exact (power_order v (by decide : (2:Rat)≠0) 12).2.trans
      (by change (12:Int)*order 2 2=12; rw [show order 2 2=1 from order_prime twoPrime]; decide)
  have sum : order 2 (4096*t.1)=order 2 4096+order 2 t.1 := v.mul _ _ (by decide) r
  omega

#print axioms norm_min
#print axioms real_of_even
#print axioms odd_den_coordinates
#print axioms four_abscissas
end AnchorCollision.Dyadic
