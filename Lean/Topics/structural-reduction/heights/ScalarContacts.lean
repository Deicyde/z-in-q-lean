import SquareClasses
import SquareGate

namespace StructuralHeights
open IndependentIndices Lean.Grind

def coordinates (q : Rat) : Pair := (q.num,(q.den:Int))
def scalarPair (u v : Int) : Pair := (u^2+2401*v^2,v^2)

theorem coordinates_primitive (q : Rat) : Primitive (coordinates q) := by
  simpa [Primitive,coordinates,Int.gcd_eq_natAbs_gcd_natAbs] using q.reduced

private theorem scalarPair_primitive (z : Rat) : Primitive (scalarPair z.num z.den) := by
  change Int.gcd (z.num^2+2401*(z.den:Int)^2) ((z.den:Int)^2)=1
  rw [Int.gcd_add_mul_right_left]
  exact Int.gcd_pow_right_of_gcd_eq_one (Int.gcd_pow_left_of_gcd_eq_one (coordinates_primitive z))

/-- The actual squared label has these reduced coordinates even when the input has a pole. -/
theorem square_label_coordinates (z : Rat) : coordinates (2401+z^2)=scalarPair z.num z.den := by
  let a := z.num^2+2401*(z.den:Int)^2
  have cp : Nat.gcd (z.den^2) a.natAbs=1 := by
    have h := scalarPair_primitive z
    change Int.gcd a ((z.den:Int)^2)=1 at h
    simpa only [Int.gcd_eq_natAbs_gcd_natAbs,Int.natAbs_pow,Int.natAbs_natCast,Nat.gcd_comm a.natAbs] using h
  have eq : (2401:Rat)+z^2 = mkRat a (z.den^2) := by
    rw [Rat.add_def']
    change mkRat ((2401:Int)*(z.den^2:Nat) + z.num^2*1) (1*z.den^2) = _
    rw [Nat.one_mul,Int.natCast_pow]
    congr 1; dsimp [a];grobner
  rw [eq]
  simp [coordinates,scalarPair,Rat.num_mkRat,Rat.den_mkRat,cp,z.den_nz,a,Int.natCast_pow] at *

def firstForm (u v : Int) := u^2+2401*v^2
def secondForm (u v : Int) := u^2+2400*v^2
def thirdForm (u v : Int) := 32*u^2+77175*v^2
def sextic (u v : Int) := firstForm u v*secondForm u v*thirdForm u v

theorem scalar_polynomial (u v : Int) :
    quintic (scalarPair u v).1 (scalarPair u v).2 = sextic u v*(u*v)^2 := by
  unfold quintic scalarPair sextic firstForm secondForm thirdForm; grobner

theorem square_label_contact {p : Nat} (hp : Prime p) (good : ¬(p:Int)∣210)
    (z : Rat) (nonzero : z.num≠0) :
    Contact p (coordinates (2401+z^2)) ↔ OddOrder p (sextic z.num z.den) := by
  rw [square_label_coordinates,contact_iff_quintic hp good _ (scalarPair_primitive z),
      scalar_polynomial,odd_times_square hp (Int.mul_ne_zero nonzero (by have := z.den_nz;omega))]

private theorem numerator_eq (z : Rat) : (z.num:Rat)=z*((z.den:Int):Rat) := by
  have h : ((z.den:Int):Rat)≠0 := fun e=>z.den_nz (by have := Rat.intCast_eq_zero_iff.mp e;omega)
  have rep := Rat.num_divInt_den z
  rw [Rat.divInt_eq_div] at rep
  exact (Rat.div_mul_cancel h).symm.trans (congrArg (fun a : Rat=>a*((z.den:Int):Rat)) rep)

/-- The cross multiplication uses the four reduced integer coordinates of the physical gate. -/
theorem physical_cross (x : Rat) :
    let z:=SquareGate.value x
    let t:=SquareGate.shift x
    (z.num+91*(z.den:Int))*(t.den:Int)^2 = 119*(z.den:Int)*t.num^2 := by
  dsimp only
  apply Rat.intCast_inj.mp
  simp only [Rat.intCast_add,Rat.intCast_mul,Rat.intCast_pow]
  rw [numerator_eq (SquareGate.value x),numerator_eq (SquareGate.shift x)]
  unfold SquareGate.value
  change ( (119 * SquareGate.shift x ^ 2 - 91) * _ + 91 * _ ) * _ = 119 * _ * _
  grobner

private theorem finite_prime (p : Nat) (big : 1<p)
    (small : ∀ i : Fin (p+1), i.val∣p → i.val=1 ∨ i.val=p) : Prime p := by
  refine ⟨big,fun d hd=>small ⟨d,?_⟩ hd⟩
  have := Nat.le_of_dvd (by omega : 0<p) hd
  omega

theorem prime17 : Prime 17 := finite_prime 17 (by decide) (by decide)
theorem prime3 : Prime 3 := finite_prime 3 (by decide) (by decide)

private theorem coprime_coordinates {p : Nat} (hp : Prime p) {x : Pair} (prim : Primitive x)
    (h : (p:Int)∣x.2) : ¬(p:Int)∣x.1 := by
  intro h'
  have div := (Int.gcd_eq_one_iff.mp prim) _ h' h
  have hi:=Nat.le_of_dvd (by decide : 0<1) (Int.ofNat_dvd_left.mp div)
  have := hp.1
  omega

/-- At 17 the physical inner square either has a pole or is congruent to -91. -/
theorem chart17 (x : Rat) :
    let z:= SquareGate.value x
    ((17:Int)∣(z.den:Int) ∧ ¬(17:Int)∣z.num) ∨
      (¬(17:Int)∣(z.den:Int) ∧ (17:Int)∣z.num+91*(z.den:Int)) := by
  let z:=SquareGate.value x
  let t:=SquareGate.shift x
  change ((17:Int)∣(z.den:Int) ∧ _) ∨ (¬(17:Int)∣(z.den:Int) ∧ _)
  by_cases h : (17:Int)∣(z.den:Int)
  · exact Or.inl ⟨h,coprime_coordinates prime17 (coordinates_primitive z) h⟩
  have eq := physical_cross x
  change (z.num+91*(z.den:Int))*(t.den:Int)^2=119*(z.den:Int)*t.num^2 at eq
  have tunit : ¬(17:Int)∣(t.den:Int) := by
    intro v
    have munit:=coprime_coordinates prime17 (coordinates_primitive t) v
    obtain ⟨k,hk⟩ := v
    rw [hk] at eq
    have div : (17:Int) ∣ 7*(z.den:Int)*t.num^2 := by
      refine ⟨(z.num+91*(z.den:Int))*k^2,?_⟩
      apply Int.eq_of_mul_eq_mul_left (a:=17) (by decide)
      calc
        _ = 119*(z.den:Int)*t.num^2 := by grobner
        _ = _ := eq.symm
        _ = _ := by grobner
    rcases (prime_dvd_mul prime17).mp div with d|d
    · exact ((prime_dvd_mul prime17).mp d).elim (by decide : ¬(17:Int)∣7) h
    · exact munit (prime_dvd_base prime17 2 d)
  apply Or.inr
  refine ⟨h,?_⟩
  have div : (17:Int)∣(z.num+91*(z.den:Int))*(t.den:Int)^2 :=
    eq ▸ ⟨7*(z.den:Int)*t.num^2,by grobner⟩
  exact ((prime_dvd_mul prime17).mp div).resolve_right (fun d=>tunit (prime_dvd_base prime17 2 d))

attribute [local instance] Semiring.natCast Ring.intCast

private theorem residue {p : Nat} [NeZero p] (a : Int) :
    (a:Fin p)=0 ↔ (p:Int)∣a := (IsCharP.intCast_eq_zero_iff p a).trans Int.dvd_iff_emod_eq_zero.symm

private theorem value_nonzero (x : Rat) : (SquareGate.value x).num≠0 := by
  let z:=SquareGate.value x
  change z.num≠0
  intro zero
  rcases chart17 x with ⟨_,h⟩|⟨nv,h⟩
  · exact h (zero ▸ Int.dvd_zero 17)
  · change (17:Int)∣z.num+91*(z.den:Int) at h
    rw [zero,Int.zero_add] at h
    exact ((prime_dvd_mul prime17).mp h).elim (by decide : ¬(17:Int)∣91) nv

private def sextic17 (u v : Fin 17) :=
  (u^2+2401*v^2)*(u^2+2400*v^2)*(32*u^2+77175*v^2)

private theorem table17 : ∀ u v : Fin 17,
    ((v=0 ∧ u≠0) ∨ (v≠0 ∧ u+91*v=0)) →
      sextic17 u v≠0 ∧ ∃ a : Fin 17, sextic17 u v=a^2 := by decide

private theorem cast_sextic17 (u v : Int) : ((sextic u v:Int):Fin 17)=sextic17 u v := by
  unfold sextic firstForm secondForm thirdForm sextic17
  simp only [Ring.intCast_add,Ring.intCast_mul,Ring.intCast_pow]
  rfl

/-- The primitive sextic is a nonzero square modulo 17 for every rational input. -/
theorem square_at_17 (x : Rat) :
    let z:=SquareGate.value x
    ¬(17:Int)∣sextic z.num z.den ∧ ∃ a : Fin 17, ((sextic z.num z.den:Int):Fin 17)=a^2 := by
  let z:=SquareGate.value x
  change ¬(17:Int)∣sextic z.num z.den ∧ _
  have alternatives := chart17 x
  have hs : ((((z.den:Int):Fin 17)=0 ∧ (z.num:Fin 17)≠0) ∨
              (((z.den:Int):Fin 17)≠0 ∧ (z.num:Fin 17)+91*((z.den:Int):Fin 17)=0)) := by
    rcases alternatives with ⟨hv,hu⟩|⟨hv,hu⟩
    · exact Or.inl ⟨(residue _).mpr hv,fun k=>hu ((residue _).mp k)⟩
    · have z' := (residue (p:=17) _).mpr hu
      simp only [Ring.intCast_add,Ring.intCast_mul] at z'
      exact Or.inr ⟨fun k=>hv ((residue _).mp k),z'⟩
  obtain ⟨unit,sq⟩ := table17 _ _ hs
  rw [←cast_sextic17] at unit sq
  exact ⟨fun d=>unit ((residue _).mpr d),sq⟩

theorem physical_contact {p : Nat} (hp : Prime p) (good : ¬(p:Int)∣210) (x : Rat) :
    let z:=SquareGate.value x
    Contact p (coordinates (SquareGate.label x)) ↔ OddOrder p (sextic z.num z.den) :=
  square_label_contact hp good _ (value_nonzero x)

theorem no_contact_17 (x : Rat) : ¬Contact 17 (coordinates (SquareGate.label x)) :=
  fun h=>(square_at_17 x).1 (odd_dvd ((physical_contact prime17 (by decide) x).mp h))

#print axioms square_label_coordinates
#print axioms physical_cross
#print axioms physical_contact
#print axioms square_at_17
#print axioms no_contact_17
end StructuralHeights
