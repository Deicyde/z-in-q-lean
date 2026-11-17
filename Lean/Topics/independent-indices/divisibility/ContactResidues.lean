import BlueprintReduction

namespace IndependentIndices
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

private theorem int_two {R : Type} [CommRing R] : ((2:Int):R)=(2:R) := Ring.intCast_ofNat 2

/-- A single identity works both before reduction (integrality) and after reduction (precision). -/
theorem subtraction {R : Type} [CommRing R] (m u n l l' : R) :
    2*(l-n) = (2-m)*(l-l') + (m*l-2*u) - ((m-2)*l'-2*(u-n)) := by
  grobner

/-- An additive module of errors, stable under integral scalars and division by the unit 2.
It can be the local valuation ring itself, or a power of its maximal ideal. -/
structure ErrorModule (R : Type) [CommRing R] where
  contains : R → Prop
  add : ∀ {x y}, contains x → contains y → contains (x+y)
  sub : ∀ {x y}, contains x → contains y → contains (x-y)
  intMul : ∀ (i : Int) {x}, contains x → contains ((i:R)*x)
  half : ∀ {x}, contains (2*x) → contains x

theorem subtract_errors {R : Type} [CommRing R] (E : ErrorModule R) (m u n : Int) (l l' : R)
    (cross : E.contains (l-l'))
    (first : E.contains ((m:R)*l-2*(u:R)))
    (second : E.contains (((m:R)-2)*l'-2*((u:R)-(n:R)))) :
    E.contains (l-(n:R)) := by
  apply E.half
  rw [subtraction (m:R) (u:R) (n:R)]
  apply E.sub _ second
  apply E.add _ first
  simpa only [Ring.intCast_sub,int_two] using E.intMul (2-m) cross

/-- The bootstrap needs integrality of the two products and of the cross difference. -/
theorem bootstrap {R : Type} [CommRing R] (E : ErrorModule R) (m : Int) (l l' : R)
    (cross : E.contains (l-l')) (left : E.contains ((m:R)*l))
    (right : E.contains (((m:R)-2)*l')) : E.contains l ∧ E.contains l' := by
  have scaled : E.contains (((2:R)-(m:R))*(l-l')) := by
    simpa only [Ring.intCast_sub,int_two] using E.intMul (2-m) cross
  have merged:=E.sub (E.add scaled left) right
  have eq : (((2:R)-(m:R))*(l-l')+(m:R)*l)-((m:R)-2)*l'=2*l := by grobner
  rw [eq] at merged
  have h := E.half merged
  have back : l-(l-l')=l' := by grobner
  exact ⟨h,back ▸ E.sub h cross⟩

theorem integer_zero {R : Type} [CommRing R] {N : Nat} [IsCharP R N] (z : Int) :
    (z:R)=0 ↔ (N:Int) ∣ z := (IsCharP.intCast_eq_zero_iff N z).trans Int.dvd_iff_emod_eq_zero.symm

theorem two_unit {R : Type} [CommRing R] {N : Nat} [IsCharP R N] (odd : N%2=1) :
    (2:R)*(((N+1)/2:Nat):R)=1 := by
  have z : ((N:Int):R)=0 := (integer_zero _).mpr (Int.dvd_refl _)
  have nz : (N:R)=0 := by simpa only [Ring.intCast_natCast] using z
  have eq : 2*((N+1)/2)=N+1 := by omega
  have h := congrArg (fun i : Nat => (i:R)) eq
  simp only [Semiring.natCast_mul,Semiring.natCast_add] at h
  rw [nz] at h
  have cast2 : ((2:Nat):R)=2 := (Semiring.ofNat_eq_natCast 2).symm
  rw [cast2,Semiring.natCast_one] at h
  grobner

theorem odd_power (p k : Nat) (h : p%2=1) : (p^k)%2=1 := by
  rw [Nat.pow_mod,h,Nat.one_pow]

/-- The primary and conjugated alternate ratios in one residue ring, with the doubled
integer index m. The precision of the first label and the other three may differ. -/
structure LogRow (R : Type) [CommRing R] (m n : Int) where
  u : Int
  primary : R
  alternate : R
  cross : primary=alternate
  primaryLog : (m:R)*primary=2*(u:R)
  alternateLog : ((m:R)-2)*alternate=2*((u:R)-(n:R))

theorem LogRow.label {R : Type} [CommRing R] {N : Nat} [IsCharP R N]
    {m n : Int} (row : LogRow R m n) (odd : N%2=1) : row.primary=(n:R) := by
  apply BlueprintReduction.shifted_residue (m:R) (2*(row.u:R)) (n:R) row.primary row.alternate 2
    (((N+1)/2:Nat):R) (two_unit odd) row.cross row.primaryLog
  rw [row.alternateLog];grobner

def lucas {R : Type} [CommRing R] (a t b : R) := t*t-a*(a-2)*t*b+(a-2)*(a-2)*b*b-1

theorem lucas_cast {R : Type} [CommRing R] (a t b : Int) :
    ((lucas a t b:Int):R)=lucas (a:R) (t:R) (b:R) := by
  simp only [lucas,Ring.intCast_sub,Ring.intCast_mul,Ring.intCast_add,int_two,Ring.intCast_one]

theorem reduced_num (n : Int) (B : Rat) :
    ((n:Rat)-B).num = n*(B.den:Int)-B.num := by
  change (Rat.sub (n:Rat) B).num=_
  simp [Rat.sub]

structure Labels where
  n₁ : Int
  n₂ : Int
  n₃ : Int
  n₄ : Int

/-- Two precisions may use residue rings of unramified split or inert completions. -/
structure Ratios (R S : Type) [CommRing R] [CommRing S] (m : Int) (ns : Labels) (B : Rat) where
  first : LogRow R m ns.n₁
  second : LogRow S m ns.n₂
  third : LogRow S m ns.n₃
  fourth : LogRow S m ns.n₄
  detector : (B.den:R)*first.primary=(B.num:R)
  lucasTest : lucas second.primary third.primary fourth.primary=0

/-- The literal source polynomial and the reduced numerator follow from ratio rows and
the two detector tests, even if the rational detector is supplied only after clearing. -/
theorem local_divisibilities {R S : Type} [CommRing R] [CommRing S] (p : Nat)
    [IsCharP R (p^10)] [IsCharP S (p^40)] (odd : p%2=1) {m : Int} {ns : Labels} {B : Rat}
    (rows : Ratios R S m ns B) :
    ((p^40:Nat):Int) ∣ lucas ns.n₂ ns.n₃ ns.n₄ ∧ ((p^10:Nat):Int) ∣ ((ns.n₁:Rat)-B).num := by
  constructor
  · apply (integer_zero (R:=S) _).mp
    rw [lucas_cast,←rows.second.label (odd_power p 40 odd),←rows.third.label (odd_power p 40 odd),
      ←rows.fourth.label (odd_power p 40 odd)]
    exact rows.lucasTest
  · rw [reduced_num];apply (integer_zero (R:=R) _).mp
    rw [Ring.intCast_sub,Ring.intCast_mul,Ring.intCast_natCast,←rows.first.label (odd_power p 10 odd)]
    have h:=rows.detector;grobner

end IndependentIndices
