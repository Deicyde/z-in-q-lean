import ComparisonChart
import SexticOrder

namespace Prime23
open Lean.Grind PhysicalProjection.Comparison
attribute [local instance] Semiring.natCast Ring.intCast
abbrev Residues (p : Nat) := Fin p × Fin p
variable {p : Nat} [NeZero p]

/-- A rational fraction with denominator one modulo p. -/
def Red (p : Nat) [NeZero p] (x : Rat) (r : Fin p) : Prop :=
  ∃ a d : Int, (d : Fin p)=1 ∧ (a : Fin p)=r ∧ x*(d:Rat)=(a:Rat)

theorem redInt (a : Int) : Red p (a:Rat) (a:Fin p) :=
  ⟨a,1,Ring.intCast_one,rfl,by simp⟩
theorem redZero : Red p 0 0 := by simpa using (redInt (p:=p) 0)
theorem redOne : Red p 1 1 := by simpa using (redInt (p:=p) 1)
theorem redTwo : Red p 2 2 := redInt 2

theorem Red.unique {x : Rat} {r s : Fin p} (h : Red p x r) (k : Red p x s) : r=s := by
  obtain ⟨a,d,du,ae,xe⟩:=h
  obtain ⟨b,e,eu,be,ye⟩:=k
  have cross : a*e=b*d := Rat.intCast_inj.mp (by
    rw [Rat.intCast_mul,Rat.intCast_mul,←xe,←ye]; grobner)
  have eq := congrArg (fun n:Int=>(n:Fin p)) cross
  simpa only [Ring.intCast_mul,du,eu,Semiring.mul_one,ae,be] using eq

theorem Red.add {x y : Rat} {r s : Fin p} (h : Red p x r) (k : Red p y s) :
    Red p (x+y) (r+s) := by
  obtain ⟨a,d,du,ae,xe⟩:=h
  obtain ⟨b,e,eu,be,ye⟩:=k
  refine ⟨a*e+b*d,d*e,by simp only [Ring.intCast_mul,du,eu,Semiring.mul_one],?_,?_⟩
  · simp only [Ring.intCast_add,Ring.intCast_mul,eu,du,ae,be,Semiring.mul_one]
  · simp only [Rat.intCast_mul,Rat.intCast_add]; grobner

theorem Red.mul {x y : Rat} {r s : Fin p} (h : Red p x r) (k : Red p y s) :
    Red p (x*y) (r*s) := by
  obtain ⟨a,d,du,ae,xe⟩:=h
  obtain ⟨b,e,eu,be,ye⟩:=k
  refine ⟨a*b,d*e,by simp only [Ring.intCast_mul,du,eu,Semiring.mul_one],?_,?_⟩
  · simp only [Ring.intCast_mul,ae,be]
  · simp only [Rat.intCast_mul]; grobner

theorem Red.neg {x : Rat} {r : Fin p} (h : Red p x r) : Red p (-x) (-r) := by
  obtain ⟨a,d,du,ae,xe⟩:=h
  exact ⟨-a,d,du,by rw [Ring.intCast_neg,ae],by rw [Rat.intCast_neg,←xe]; grobner⟩

theorem Red.invOne (hp : 1<p) {x : Rat} (h : Red p x 1) : x≠0 ∧ Red p x⁻¹ 1 := by
  have apart : (0:Fin p)≠1 := by
    intro eq
    have e := congrArg Fin.val eq
    change 0=1%p at e
    rw [Nat.mod_eq_of_lt hp] at e
    omega
  have live : x≠0 := fun z=>apart (redZero.unique (z ▸ h))
  obtain ⟨a,d,du,ae,xe⟩:=h
  refine ⟨live,⟨d,a,ae,du,?_⟩⟩
  rw [←xe,←Rat.mul_assoc,Rat.inv_mul_cancel _ live,Rat.one_mul]

/-- A nonzero residue gives the exact rational valuation. -/
theorem Red.unit_order (hp : BinaryQuartic.Prime p) {x : Rat} {r : Fin p}
    (h : Red p x r) (unit : r≠0) : x≠0 ∧ StructuralReduction.order p x=0 := by
  have ziff (u : Int) : (u:Fin p)=0 ↔ (p:Int)∣u :=
    (IsCharP.intCast_eq_zero_iff p u).trans Int.dvd_iff_emod_eq_zero.symm
  obtain ⟨a,d,du,ae,xe⟩:=h
  have au : ¬(p:Int)∣a := fun hd=>unit (ae ▸ (ziff a).mpr hd)
  have dz : (1:Fin p)≠0 := by
    intro eq
    have e := congrArg Fin.val eq
    change 1%p=0 at e
    rw [Nat.mod_eq_of_lt hp.1] at e
    omega
  have dd : ¬(p:Int)∣d := fun hd=>dz (du ▸ (ziff d).mpr hd)
  have az : a≠0 := fun z=>au (z ▸ Int.dvd_zero _)
  have dn : d≠0 := fun z=>dd (z ▸ Int.dvd_zero _)
  obtain ⟨nz,ord⟩:=StructuralReduction.order_of_fraction hp az dn xe
  have va:=StructuralReduction.order_int_unit hp au
  have vd:=StructuralReduction.order_int_unit hp dd
  rw [StructuralReduction.order_int hp] at va vd
  exact ⟨nz,by omega⟩

def PairRed (p : Nat) [NeZero p] (x : Q2) (r : Residues p) : Prop :=
  Red p x.1 r.1 ∧ Red p x.2 r.2

def plus (x y : Q2) : Q2 := (x.1+y.1,x.2+y.2)
def scale (s : Rat) (x : Q2) : Q2 := (s*x.1,s*x.2)
def inverse (x : Q2) : Q2 := (x.1*(norm x)⁻¹,(-x.2)*(norm x)⁻¹)
def addR (x y : Residues p) : Residues p := (x.1+y.1,x.2+y.2)
def mulR (x y : Residues p) : Residues p := (x.1*y.1+2*x.2*y.2,x.1*y.2+x.2*y.1)
def scaleR (s : Fin p) (x : Residues p) : Residues p := (s*x.1,s*x.2)

theorem pairOne : PairRed p (1,0) (1,0) := ⟨redOne,redZero⟩
theorem pairZero : PairRed p (0,0) (0,0) := ⟨redZero,redZero⟩
theorem PairRed.unique {x : Q2} {r s : Residues p} (h : PairRed p x r) (k : PairRed p x s) :
    r=s := Prod.ext (h.1.unique k.1) (h.2.unique k.2)
theorem PairRed.add {x y : Q2} {r s : Residues p} (h : PairRed p x r) (k : PairRed p y s) :
    PairRed p (plus x y) (addR r s) := ⟨h.1.add k.1,h.2.add k.2⟩
theorem PairRed.mul {x y : Q2} {r s : Residues p} (h : PairRed p x r) (k : PairRed p y s) :
    PairRed p (times x y) (mulR r s) :=
  ⟨(h.1.mul k.1).add (((redTwo.mul h.2).mul k.2)),(h.1.mul k.2).add (h.2.mul k.1)⟩
theorem PairRed.scale {s : Rat} {k : Fin p} {x : Q2} {r : Residues p}
    (a : Red p s k) (h : PairRed p x r) : PairRed p (scale s x) (scaleR k r) :=
  ⟨a.mul h.1,a.mul h.2⟩

theorem PairRed.norm {x : Q2} {r : Residues p} (h : PairRed p x r) :
    Red p (PhysicalProjection.Comparison.norm x) (r.1*r.1+ -(2*r.2*r.2)) := by
  have R := (h.1.mul h.1).add (((redTwo.mul h.2).mul h.2).neg)
  rw [show PhysicalProjection.Comparison.norm x=x.1*x.1+ -(2*x.2*x.2) by
    dsimp [PhysicalProjection.Comparison.norm]; grobner]
  exact R

theorem inverse_clears {x : Q2} (hn : norm x≠0) : times x (inverse x)=(1,0) := by
  have eq := Rat.mul_inv_cancel _ hn
  apply Prod.ext
  · change x.1*(x.1*(norm x)⁻¹)+2*x.2*((-x.2)*(norm x)⁻¹)=1
    rw [←eq]
    dsimp [norm]; grobner
  · change x.1*((-x.2)*(norm x)⁻¹)+x.2*(x.1*(norm x)⁻¹)=0
    grobner

theorem PairRed.invOne (hp : 1<p) {x : Q2} (h : PairRed p x (1,0)) :
    PhysicalProjection.Comparison.norm x≠0 ∧ PairRed p (inverse x) (1,0) := by
  have normRed : Red p (PhysicalProjection.Comparison.norm x) 1 := by
    simpa [Semiring.mul_zero,Semiring.mul_one,Semiring.zero_mul,
      AddCommGroup.neg_zero,AddCommMonoid.add_zero] using h.norm
  obtain ⟨hn,rr⟩:=normRed.invOne hp
  refine ⟨hn,?_,?_⟩
  · simpa only [Semiring.mul_one] using h.1.mul rr
  · simpa only [AddCommGroup.neg_zero,Semiring.mul_one] using h.2.neg.mul rr

theorem tm_assoc (a b c : Q2) : times (times a b) c=times a (times b c) := by
  apply Prod.ext <;> dsimp [times] <;> grobner
theorem tm_one (a : Q2) : times a (1,0)=a := by
  apply Prod.ext <;> dsimp [times] <;> grobner

#print axioms Red.unit_order
#print axioms PairRed.invOne
end Prime23
