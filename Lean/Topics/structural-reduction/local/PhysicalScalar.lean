import PoleWireIdentities

namespace StructuralReduction.Wires
open BinaryQuartic ProgressionWitnesses.SingleContact Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

inductive Frame where
  | first | second | third | scalar

def Frame.address : Frame→Nat
  | .first=>19788 | .second=>19897 | .third=>21391 | .scalar=>21764

def Frame.input (x : Nat→Rat) : Frame→Rat
  | .first=>x 52 | .second=>x 87 | .third=>x 122 | .scalar=>kappa*x 133

private theorem point_of_residual {b t s j : Rat} (eq : residual b t s j=0) :
    ThreeCoordinates.Sextic (17*b) (289-17*b) := by
  exact ⟨t,s,j,by unfold residual at eq;grobner⟩

/-- Literal signed outputs of the 22,048-node tape, on every rational assignment
and for every completion of its instruction table away from the certified footprint. -/
theorem frame_sextic (f : Frame) (g : Nat→Op) (x : Nat→Rat)
    (zero : read (complete g) x f.address=0) :
    ThreeCoordinates.Sextic (17*f.input x) (289-17*f.input x) := by
  cases f with
  | first => rw [Frame.address,sextic19788] at zero;exact point_of_residual zero
  | second => rw [Frame.address,sextic19897] at zero;exact point_of_residual zero
  | third => rw [Frame.address,sextic21391] at zero;exact point_of_residual zero
  | scalar => rw [Frame.address,sextic21764] at zero;exact point_of_residual zero

theorem frame_prime_order (f : Frame) (g : Nat→Op) (x : Nat→Rat) {p : Nat}
    (hp : Prime p) (large : 5≤p) (away : p≠17) (zero : read (complete g) x f.address=0)
    (live : f.input x≠0) (odd : OddOrder (order p (f.input x))) : 0<order p (f.input x) :=
  good_prime_positive hp large away live odd (frame_sextic f g x zero)

theorem frame_seventeen (f : Frame) (g : Nat→Op) (x : Nat→Rat)
    (zero : read (complete g) x f.address=0) (live : f.input x≠0)
    (even : ∃k,order 17 (f.input x)=2*k) : 0<order 17 (f.input x) :=
  seventeen_even_positive live even (frame_sextic f g x zero)

private theorem cancel {r a b : Rat} (hr : r≠0) (eq : a*r=b*r) : a=b := by grind

private theorem cancel_scale {v : Rat} (h : (67830:Rat)^48*v=0) : v=0 :=
  (Rat.mul_eq_zero.mp h).resolve_left (by decide)

private theorem reciprocal_values {r u v q m d b : Rat} (hr : r≠0) (hq : q≠0)
    (num : d*r^16=r*u^2+v^2) (recip : m*d*r^16=d^2+r^3*q^2) (corr : -m^2+b*r^3=0) :
    ScalarValues r u v q (r^16*(d/r)) (m/r) b := by
  have D:=Rat.div_mul_cancel (a:=d) hr
  have W:=Rat.div_mul_cancel (a:=m) hr
  have L:=Rat.div_mul_cancel (a:=v^2) hr
  have r2 : r^2≠0 := by grind
  have first : r^16*(d/r)=u^2+v^2/r := by
    apply cancel hr
    calc r^16*(d/r)*r = r^16*((d/r)*r) := by grobner
         _ = d*r^16 := by rw [D,Rat.mul_comm]
         _ = r*u^2+v^2 := num
         _ = (u^2+v^2/r)*r := by rw [Rat.add_mul,L,Rat.mul_comm r]
  have second : (d/r)*(r^16*(m/r))=(d/r)^2+r*q^2 := by
    apply cancel r2
    calc (d/r)*(r^16*(m/r))*r^2=((m/r)*r)*((d/r)*r)*r^16 := by grobner
         _=d^2+r^3*q^2 := by rw [D,W,recip]
         _=((d/r)*r)^2+r^3*q^2 := by rw [D]
         _=((d/r)^2+r*q^2)*r^2 := by grobner
  have wire : m^2=r^2*(m/r)^2 := by calc
    _=((m/r)*r)^2 := congrArg (·^2) W.symm
    _=_ := by grobner
  have link:=scalar_signed_link (κ:=b) (b₀:=1) hr wire (by rw [Rat.mul_one];exact corr)
  rw [Rat.mul_one] at link
  exact scalar_from_cleared hr hq (Rat.mul_comm r (v^2/r) ▸ L) first second rfl link

/-- Read the scalar values U,W,b from signed residuals 565,512,492. -/
theorem scalar_wires (g : Nat→Op) (x : Nat→Rat) (hr : contact (x 1)≠0) (hq : normInput x≠0)
    (num : read (complete g) x 21956=0) (recip : read (complete g) x 21921=0)
    (corr : read (complete g) x 163=0) :
    let r:=contact (x 1)
    ScalarValues r (x 130) (x 131) (normInput x) (r^16*((x 134)/r)) ((x 132)/r) (kappa*x 133) := by
  rw [numerator_row,gate_y2] at num
  rw [reciprocal_row,gate_y2] at recip
  rw [correction] at corr
  dsimp only
  let r:=contact (x 1)
  have hn := cancel_scale num
  have hw := cancel_scale recip
  change r*(x 130)^2+(x 131)^2-(x 134)*r^16=0 at hn
  change (x 132)*(x 134)*r^16-(x 134)^2-r^3*(normInput x)^2=0 at hw
  have first {a b : Rat} (h : a-b=0) : b=a := by grobner
  have second {a b c : Rat} (h : a-b-c=0) : a=b+c := by grobner
  exact reciprocal_values hr hq (first hn) (second hw) corr

private theorem reduced_den_order {p : Nat} (hp : Prime p) {b : Rat} (dn : p∣b.den) :
    b≠0 ∧ order p b = -(natOrder p b.den:Int) := by
  have nz : b≠0 := by
    intro e;subst b;change p∣1 at dn;have := Nat.eq_one_of_dvd_one dn;have := hp.1;omega
  have unit : ¬(p:Int)∣b.num := fun dd=>Nat.not_coprime_of_dvd_of_dvd hp.1 (Int.ofNat_dvd_left.mp dd) dn b.reduced
  have h:=order_int_unit hp unit
  rw [order_int hp] at h
  exact ⟨nz,by unfold order;omega⟩

/-- Exponents in the canonical positive denominator are even away from 17 at the
good primes, and an exponent at 17, when present, is odd. -/
theorem frame_denominator (f : Frame) (g : Nat→Op) (x : Nat→Rat)
    (zero : read (complete g) x f.address=0) {p : Nat} (hp : Prime p) (large : 5≤p)
    (present : p∣(f.input x).den) :
    (p≠17 → ¬OddOrder (natOrder p (f.input x).den:Int)) ∧
    (p=17 → ¬∃k : Int, (natOrder p (f.input x).den:Int)=2*k) := by
  obtain ⟨nz,eq⟩:=reduced_den_order hp present
  constructor
  · rintro away ⟨k,hk⟩
    have pos:=frame_prime_order f g x hp large away zero nz ⟨-k-1,by omega⟩
    omega
  · rintro rfl ⟨k,hk⟩
    have pos:=frame_seventeen f g x zero nz ⟨-k,by omega⟩
    omega

variable {p : Nat} {K : Type} [Field K] {w : ExtensionPlace p K}
variable {G G' : Type} [IntModule G] [IntModule G']
variable (chart : MultiplicationChart p w G) (other : MultiplicationChart p w G')

private theorem evaluated_norm (x : Nat→Rat) {rho : K} (root : rho^2=2) :
    w.incl.map (normInput x)=(w.incl.map (x 126)+w.incl.map (x 127)*rho)*
       (w.incl.map (x 126)+w.incl.map (x 127)*(-rho)) := by
  have two : w.incl.map 2=(2:K) := by
    calc _=w.incl.map ((2:Int):Rat) := congrArg w.incl.map (by decide)
         _=((2:Int):K) := w.incl.int 2
         _=2 := by grobner
  rw [normInput,w.incl.sub,w.incl.pow,w.incl.mul,two,w.incl.pow]
  grobner

/-- The scalar divisor at one actual odd contact, directly from four signed
physical instructions and the two affine/group evaluations at the same private index. -/
theorem physical_scalar_divisor (g : Nat→Op) (x : Nat→Rat) {m n : Int} {rho : K}
    (hp : Prime p) (large : 5≤p) (away : p≠17)
    (hr : contact (x 1)≠0) (positive : 0<order p (contact (x 1))) (odd : OddOrder (order p (contact (x 1))))
    (num : read (complete g) x 21956=0) (recip : read (complete g) x 21921=0)
    (corr : read (complete g) x 163=0) (pole : read (complete g) x 21764=0)
    (left : ScalarBranch chart m n (x 130) (x 131) rho)
    (right : ScalarBranch other m n (x 130) (x 131) (-rho))
    (leftF : left.shared.f=w.incl.map (x 126)+w.incl.map (x 127)*rho)
    (rightF : right.shared.f=w.incl.map (x 126)+w.incl.map (x 127)*(-rho)) : ((p^17:Nat):Int)∣n-1 := by
  have norm := evaluated_norm (w:=w) x left.root
  rw [←leftF,←rightF] at norm
  have qn : normInput x≠0 := fun z=>(w.product left.shared.live.1 right.shared.live.1).1
    (by rw [←norm,z,w.incl.zero])
  exact scalar_index_divisor chart other hp large away positive odd hr (scalar_wires g x hr qn num recip corr)
    (frame_sextic .scalar g x pole) left right norm

end StructuralReduction.Wires
