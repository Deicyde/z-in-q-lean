import RationalPrimeOrder
import ThreeCoordinates

namespace StructuralReduction
open BinaryQuartic ProgressionWitnesses.SingleContact

theorem power_order (v : RationalOrder) {a : Rat} (ha : a ≠ 0) (n : Nat) :
    a^n ≠ 0 ∧ v.ord (a^n)=(n:Int)*v.ord a := by
  induction n with
  | zero => rw [Rat.pow_zero,v.one];exact ⟨by decide,by simp⟩
  | succ k ih =>
    rw [Rat.pow_succ]
    refine ⟨by grind [Rat.mul_eq_zero],?_⟩
    rw [v.mul _ _ ih.1 ha,ih.2,Int.natCast_succ,Int.add_mul,Int.one_mul]

/-- The two signed factors have the same finite order if the two inputs have different
orders. Either input can vanish; the other then determines both orders. -/
private theorem paired (v : RationalOrder) (three : v.ord 3=0) {x y : Rat}
    (live : x≠0 ∨ y≠0) (unequal : x≠0 → y≠0 → v.ord x ≠ v.ord y) :
    x-y≠0 ∧ x+3*y≠0 ∧ v.ord (x-y)=v.ord (x+3*y) := by
  by_cases yz : y=0
  · have hx:=live.resolve_right (fun ne => ne yz)
    rw [yz,show x-(0:Rat)=x by grobner,Rat.mul_zero,Rat.add_zero];exact ⟨hx,hx,rfl⟩
  have hy : 3*y≠0 := by grind [Rat.mul_eq_zero]
  have vy : v.ord (3*y)=v.ord y := by rw [v.mul _ _ (by decide) yz,three,Int.zero_add]
  by_cases xz : x=0
  · rw [xz,show (0:Rat)-y= -y by grobner,Rat.zero_add]
    exact ⟨by grind,hy,(v.neg y yz).trans vy.symm⟩
  have d:=unequal xz yz
  have hm:=v.addUnequal x (-y) xz (by grind) (by rw [v.neg y yz];exact d)
  have hp:=v.addUnequal x (3*y) xz hy (by rw [vy];exact d)
  rw [Rat.sub_eq_add_neg]
  exact ⟨hm.1,hp.1,by rw [hm.2,hp.2,v.neg _ yz,vy]⟩

/-- On a literal rational row, odd order of B forces even order of nonzero d.
This uses the separate factors on both sides. It includes zero slopes and derives
nonvanishing of the sextic multiplier. -/
theorem sextic_even_target (v : RationalOrder) (three : v.ord 3=0) {B d : Rat}
    (hB : B≠0) (hd : d≠0) (odd : OddOrder (v.ord B))
    (point : ThreeCoordinates.Sextic B d) : ∃ k : Int, v.ord d=2*k := by
  obtain ⟨t,s,j,eq⟩:=point
  obtain ⟨i,hi⟩:=odd
  have distinct (a : Rat) (h : a^2≠0) : v.ord (a^2)≠v.ord B := by
    have az : a≠0 := fun z=>h (by rw [z];decide)
    have squared:=(power_order v az 2).2
    omega
  obtain ⟨lt,rt,tord⟩:=paired v three (x:=t^2) (y:=B) (Or.inr hB) (fun h _ => distinct t h)
  obtain ⟨ls,rs,sord⟩:=paired v three (x:=B) (y:=s^2) (Or.inl hB) (fun _ h => Ne.symm (distinct s h))
  have rhs : d*(B-s^2)*(B+3*s^2) ≠ 0 := by grind [Rat.mul_eq_zero]
  have jz : j≠0 := fun z => rhs (by rw [←eq,z];grobner)
  obtain ⟨j2,jo⟩:=power_order v jz 2
  have e:=congrArg v.ord eq
  rw [v.mul _ _ (by grind [Rat.mul_eq_zero]) rt,v.mul _ _ j2 lt,jo,
      v.mul _ _ (by grind [Rat.mul_eq_zero]) rs,v.mul _ _ hd ls,tord,sord] at e
  exact ⟨v.ord j+v.ord (t^2+3*B)-v.ord (B+3*s^2),by omega⟩

/-- In this normalization the uniform statement is ord(b)≥ord(17)
whenever ord(17)+ord(b) is odd. No classification or local-point hypothesis
other than the three actual rational coordinates enters the proof. -/
theorem sextic_threshold (v : RationalOrder) (three : v.ord 3=0) {b : Rat}
    (hb : b≠0) (odd : OddOrder (v.ord 17+v.ord b))
    (point : ThreeCoordinates.Sextic (17*b) (289-17*b)) : v.ord 17≤v.ord b := by
  have hB : 17*b≠0 := by grind [Rat.mul_eq_zero]
  have oB := v.mul 17 b (by decide) hb
  have o289 : v.ord 289=2*v.ord 17 := by
    rw [show (289:Rat)=(17:Rat)^2 by decide];exact (power_order v (by decide) 2).2
  apply Int.le_of_not_gt
  intro low
  have opp : -(17*b)≠0 := by grind
  have neg := v.neg _ hB
  have out := v.addUnequal 289 (-(17*b)) (by decide) opp (by omega)
  have eqd : (289:Rat)-17*b=289+ -(17*b) := Rat.sub_eq_add_neg ..
  have dord : v.ord (289-17*b)=v.ord 17+v.ord b := by
    rw [eqd,out.2,Int.min_eq_right (by omega),neg,oB]
  obtain ⟨k,hk⟩:=sextic_even_target v three hB (eqd ▸ out.1) (oB ▸ odd) point
  obtain ⟨j,hj⟩:=odd
  omega

/-- Finite divisor certificate for an ordinary prime. -/
theorem prime_of_finite {p : Nat} (size : 2≤p)
    (small : ∀ d : Fin (p+1), d.val ∣ p → d.val=1 ∨ d.val=p) : Prime p := by
  refine ⟨size,fun d hd=>small ⟨d,?_⟩ hd⟩
  have le := Nat.le_of_dvd (by omega : 0<p) hd
  omega

theorem prime17 : Prime 17 := prime_of_finite (by decide) (by decide)

theorem seventeen_unit {p : Nat} (hp : Prime p) (away : p≠17) : order p 17=0 := by
  apply order_nat_unit (n:=17) hp
  intro d
  obtain u|s:=prime17.2 p d
  · have := hp.1;omega
  · exact away s

theorem three_unit {p : Nat} (hp : Prime p) (large : 5≤p) : order p 3=0 := by
  apply order_nat_unit (n:=3) hp
  intro d;have := Nat.le_of_dvd (by decide : 0<3) d;omega

/-- At primes at least five away from 17 every odd order on a sextic solution is positive. -/
theorem good_prime_positive {p : Nat} (hp : Prime p) (large : 5≤p) (away : p≠17) {b : Rat}
    (hb : b≠0) (odd : OddOrder (order p b))
    (point : ThreeCoordinates.Sextic (17*b) (289-17*b)) : 0<order p b := by
  have u:=seventeen_unit hp away
  have both : OddOrder ((primeOrder p hp).ord 17+(primeOrder p hp).ord b) := by
    change OddOrder (order p 17+order p b);simpa only [u,Int.zero_add] using odd
  have low:=sextic_threshold (primeOrder p hp) (three_unit hp large) hb both point
  change order p 17≤order p b at low
  obtain ⟨j,hj⟩:=odd;omega

/-- Exactly the excluded order parity changes at 17. This is the necessary direction:
a nonzero coefficient of even order on a rational row must have positive order. -/
theorem seventeen_even_positive {b : Rat} (hb : b≠0) (even : ∃ k : Int, order 17 b=2*k)
    (point : ThreeCoordinates.Sextic (17*b) (289-17*b)) : 0<order 17 b := by
  have op : order 17 17=1 := order_prime prime17
  obtain ⟨k,hk⟩:=even
  have both : OddOrder ((primeOrder 17 prime17).ord 17+(primeOrder 17 prime17).ord b) :=
    ⟨k,by change order 17 17+order 17 b=2*k+1;omega⟩
  have low:=sextic_threshold (primeOrder 17 prime17) (three_unit prime17 (by decide)) hb both point
  change order 17 17≤order 17 b at low
  omega

end StructuralReduction
