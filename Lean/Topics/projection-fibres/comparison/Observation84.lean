import LocalCharts
import Integral84
namespace ProjectionFibres.Comparison
open StructuralReduction StructuralReduction.Transfer84 WitnessTransfer WitnessTransfer.Local WitnessTransfer.Height
open IndependentIndices BinaryQuartic ProgressionWitnesses.SingleContact Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

private theorem natMap {O K : Type} [CommRing O] [CommRing K] (h : RingMap O K) (n : Nat) :
    h.map (n:O)=(n:K) := by simpa only [Ring.intCast_natCast] using h.int (n:Int)
private theorem twoMap {O K : Type} [CommRing O] [CommRing K] (h : RingMap O K) : h.map 2=(2:K) := by
  calc _=h.map ((2:Int):O) := congrArg _ (Ring.intCast_ofNat 2).symm
       _=((2:Int):K) := h.int _
       _=2 := Ring.intCast_ofNat 2
private theorem mapLucas {O K : Type} [CommRing O] [CommRing K] (h : RingMap O K) (a b c : O) :
    h.map (IndependentIndices.lucas a b c)=IndependentIndices.lucas (h.map a) (h.map b) (h.map c) := by
  simp only [IndependentIndices.lucas,h.add,h.mul,h.sub,h.one,twoMap h]

variable {p : Nat} {K : Type} [Field K] {w : ExtensionPlace p K} (o : LocalSetup p K w)

private theorem deep_mul {k : Int} {a b : K} (a0 : w.deep 0 a) (bk : w.deep k b) : w.deep k (a*b) := by
  intro ne
  have aa : a≠0 := fun z=>ne (by rw [z,Semiring.zero_mul])
  have bb : b≠0 := fun z=>ne (by rw [z,Semiring.mul_zero])
  have :=a0 aa;have :=bk bb;rw [w.mul _ _ aa bb];omega

private theorem multiplyDen (hp : Prime p) (n : Nat) : w.deep 0 (n:K) := by
  intro nn
  have nz : (n:Int)≠0 := by
    intro z
    have h : n=0:=by omega
    subst n
    exact nn Semiring.natCast_zero
  obtain ⟨_,e⟩:=w.on_int nz
  rw [Ring.intCast_natCast,order_int hp] at e
  omega

private theorem ratDen (B : Rat) : B*(B.den:Rat)=(B.num:Rat) := by
  have e:=Rat.num_divInt_den B
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at e
  exact (congrArg (fun r:Rat=>r*(B.den:Rat)) e.symm).trans
    (Rat.div_mul_cancel (fun z=>B.den_nz (Rat.natCast_eq_zero_iff.mp z)))

theorem LocalSetup.inputTest (hp : Prime p) {B : Rat} {l : o.O} (v : w.deep 10 (o.incl.map l-w.incl.map B)) :
    letI:=o.ten.ring
    (B.den:o.ten.carrier)*o.red10.map l=(B.num:o.ten.carrier) := by
  letI:=o.ten.ring
  letI:=o.ten.characteristic
  have mul:=deep_mul (multiplyDen (w:=w) hp B.den) v
  have d:=congrArg w.incl.map (ratDen B)
  rw [w.incl.mul,natMap,w.incl.int] at d
  have ident : o.incl.map ((B.den:o.O)*l-(B.num:o.O))=(B.den:K)*(o.incl.map l-w.incl.map B) := by
    rw [o.incl.sub,o.incl.mul,natMap,o.incl.int];grobner
  rw [←ident] at mul
  have e:=o.reduce o.red10 _ mul
  rw [o.red10.sub,o.red10.mul,natMap,o.red10.int] at e
  grobner

theorem LocalSetup.lucasTest {a b c : o.O} (v : w.deep 40
    (IndependentIndices.lucas (o.incl.map a) (o.incl.map b) (o.incl.map c))) :
    letI:=o.forty.ring
    IndependentIndices.lucas (o.red40.map a) (o.red40.map b) (o.red40.map c)=0 := by
  letI:=o.forty.ring
  letI:=o.forty.characteristic
  rw [←mapLucas o.incl] at v
  have e:=o.reduce o.red40 _ v
  rwa [mapLucas] at e

variable [IsCharP K 0]

abbrev NamedRow (f : Frame) (x : Fin 84→Rat) (m n : Int) (r : K) (i : Fin 4) (short : Bool) :=
  RowGeometry o short m n r (((f.primary x) i).eval w r) (((f.alt x) i).eval w r)
    (((f.refs x).nums i).eval w r) ((f.refs x).ref.eval w r)
    (((f.refs x).secondNums i).eval w r) ((f.refs x).secondRef.eval w r)

structure FourRows (x : Fin 84→Rat) (f : Frame) (m : Int) (ns : Labels) (r : K) where
  a : NamedRow o f x m ns.n₁ r 0 true
  b : NamedRow o f x m ns.n₂ r 1 false
  c : NamedRow o f x m ns.n₃ r 2 false
  d : NamedRow o f x m ns.n₄ r 3 false

theorem fourObservations (x : Fin 84→Rat) (f : Frame) {m : Int} {ns : Labels} {r : K}
    (g : FourRows o x f m ns r) (hp : Prime p) (large : 5≤p) (root : r^2=2)
    (ratios : TypedDepths w r (f.primary x) (f.alt x) (SquareGate.label (cell x 1)))
    (recips : ReciprocalDepths w r (f.refs x)) : Nonempty (PrimeInputs p m ns (SquareGate.label (cell x 1))) := by
  have odd : p%2=1 := by
    by_cases even : p%2=0
    · rcases hp.2 2 (Nat.dvd_of_mod_eq_zero even) with h|h <;> omega
    · omega
  refine ⟨{
      integers:=o.O
      coeffs:=K
      residue:=o.k
      integersRing:=o.ringO
      coefficientField:=inferInstance
      characteristic:=inferInstance,residueField:=o.fieldk,incl:=o.incl,injective:=o.injective,
      place:=o.place,odd:=odd,ten:=o.ten,forty:=o.forty,red10:=o.red10,red40:=o.red40,
      a:=g.a.recover o hp large root recips.ref recips.secondRef ratios.cross1,
      b:=g.b.recover o hp large root recips.ref recips.secondRef ratios.cross2,
      c:=g.c.recover o hp large root recips.ref recips.secondRef ratios.cross3,
      d:=g.d.recover o hp large root recips.ref recips.secondRef ratios.cross4,
      za:=g.a.numeratorZeros o hp large root (recips.nums 0) (recips.secondNums 0),
      zb:=g.b.numeratorZeros o hp large root (recips.nums 1) (recips.secondNums 1),
      zc:=g.c.numeratorZeros o hp large root (recips.nums 2) (recips.secondNums 2),
      zd:=g.d.numeratorZeros o hp large root (recips.nums 3) (recips.secondNums 3),
      detector:=?_,lucasTest:=?_}⟩
  · intro l eq
    have id:=g.a.ratioValue o l eq
    apply o.inputTest hp
    rw [id];exact ratios.detector
  · intro a b c ea eb ec
    apply o.lucasTest
    rw [g.b.ratioValue o a ea,g.c.ratioValue o b eb,g.d.ratioValue o c ec]
    exact ratios.lucas

end ProjectionFibres.Comparison
