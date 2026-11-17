import PhysicalReferences
import EllipticFrame

namespace ProjectionFibres.Comparison
open StructuralReduction WitnessTransfer WitnessTransfer.Local IndependentIndices BinaryQuartic Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

/-- An integral ring of the chosen completion, with the prime-power ideals and reductions. -/
structure LocalSetup (p : Nat) (K : Type) [Field K] (w : ExtensionPlace p K) where
  O : Type
  k : Type
  [ringO : CommRing O]
  [fieldk : Field k]
  [chark : IsCharP k p]
  incl : RingMap O K
  injective : Function.Injective incl.map
  place : WitnessTransfer.Local.Place O k
  lifts : ∀ (n : Nat) (a : K), w.deep (n:Int) a → ∃ e : O, a=(p:K)^n*incl.map e
  ten : Residue (p^10)
  forty : Residue (p^40)
  red10 : @RingMap O ten.carrier _ ten.ring
  red40 : @RingMap O forty.carrier _ forty.ring

attribute [instance] LocalSetup.ringO LocalSetup.fieldk LocalSetup.chark

private theorem mappedNat {R S : Type} [CommRing R] [CommRing S] (h : RingMap R S) (n : Nat) :
    h.map (n:R)=(n:S) := by
  have e:=h.int (n:Int)
  simpa only [Ring.intCast_natCast] using e

variable {p : Nat} {K : Type} [Field K] {w : ExtensionPlace p K}
variable (o : LocalSetup p K w)

theorem LocalSetup.splitValue (n : Nat) (z : o.O) (depth : w.deep (n:Int) (o.incl.map z)) :
    ∃ e : o.O,z=(p:o.O)^n*e := by
  obtain ⟨e,eq⟩:=o.lifts n _ depth
  refine ⟨e,o.injective ?_⟩
  rw [o.incl.mul,o.incl.pow,mappedNat,eq]

theorem LocalSetup.reduce {R : Type} [CommRing R] {n : Nat} [IsCharP R (p^n)] (red : RingMap o.O R)
    (z : o.O) (depth : w.deep (n:Int) (o.incl.map z)) : red.map z=0 := by
  obtain ⟨g,h⟩:=o.splitValue n z depth
  have zero : (p:R)^n=0 := by rw [←Semiring.natCast_pow];exact (IsCharP.natCast_eq_zero_iff _ _).mpr (Nat.mod_self _)
  rw [h,red.mul,red.pow,mappedNat,zero,Semiring.zero_mul]

theorem LocalSetup.residueZero (z : o.O) (deep : w.deep 1 (o.incl.map z)) : o.place.residue.map z=0 := by
  obtain ⟨a,h⟩:=o.splitValue 1 z deep
  have zero : (p:o.k)=0 := (IsCharP.natCast_eq_zero_iff _ _).mpr (Nat.mod_self _)
  rw [h,Semiring.pow_one,o.place.residue.mul,mappedNat,zero,Semiring.zero_mul]

/-- These data link one formal parameter pair to its actual affine reciprocal wires. -/
structure SourceParameters (side : Side o.O) (D nx ry : K) where
  numerator : AffineValue D (o.incl.map side.x)
  reference : AffineValue D (o.incl.map side.y)
  numValue : numerator.f=nx
  refValue : reference.f=ry

/-- Joined group-multiple and mixed-reference charts, before the pole supplies their depths and cross error. -/
structure RowGeometry [IsCharP K 0] (short : Bool) (m n : Int) (r L A fn fr an ar : K) where
  primary : Side o.O
  alternate : Side o.O
  u : Int
  firstPair : JoinedPair o.incl .raw primary m (2*u)
  secondPair : JoinedPair o.incl (altChart short) alternate (m-2) (2*(u-n))
  firstPoint : primary.x*firstPair.numerator.multiplierTail=primary.y*firstPair.reference.multiplierTail
  secondPoint : alternate.x*secondPair.numerator.multiplierTail=alternate.y*secondPair.reference.multiplierTail
  firstChart : SourceParameters o primary ((3-r)^2) fn fr
  secondChart : SourceParameters o alternate ((3-(-r))^2) an ar
  firstRatio : o.incl.map (primary.x*primary.nx)=o.incl.map (primary.y*primary.ry)*L
  secondRatio : o.incl.map (alternate.x*alternate.nx)=o.incl.map (alternate.y*alternate.ry)*A

private theorem parameterDepth {D z : K} (hp : Prime p) (unit : w.deep 0 D) (a : AffineValue D z)
    {k e : Int} (v : w.deep k a.f) (pos : 0<k) (budget : 2*(e-1)<k) : w.deep e z := by
  have vf:=v a.live.1
  have para:=formal_parameter w hp unit a (by omega)
  intro _;omega

variable [IsCharP K 0] {short : Bool} {m n : Int} {r L A fn fr an ar : K}

noncomputable def RowGeometry.recover (s : RowGeometry o short m n r L A fn fr an ar) (hp : Prime p) (large : 5≤p) (root : r^2=2)
    (vfr : w.deep 40 fr) (var' : w.deep 1 ar) (cross : w.deep ((precision short:Int)) (L-A)) :
    PhysicalRow o.incl p short m n := by
  have D:=(curve_coeffs w hp large root).2.2
  have D':=(curve_coeffs w hp large (show (-r)^2=2 by grobner)).2.2
  have depth1:=parameterDepth hp D s.firstChart.reference (s.firstChart.refValue ▸ vfr) (by decide) (e:=20) (by decide)
  have depth2:=parameterDepth hp D' s.secondChart.reference (s.secondChart.refValue ▸ var') (by decide) (e:=1) (by decide)
  let d:=o.lifts (precision short) (L-A) cross
  let g:=Classical.choose d
  have eq : L-A=(p:K)^precision short*o.incl.map g := Classical.choose_spec d
  refine ⟨s.primary,s.alternate,s.u,s.firstPair,s.secondPair,s.firstPoint,s.secondPoint,
    o.splitValue 20 _ depth1,o.splitValue 1 _ depth2,g,?_⟩
  apply o.injective
  have f:=s.firstRatio
  have a:=s.secondRatio
  simp only [o.incl.mul] at f a
  simp only [o.incl.sub,o.incl.mul,o.incl.pow,mappedNat]
  rw [←eq]
  grobner

theorem RowGeometry.numeratorZeros (s : RowGeometry o short m n r L A fn fr an ar)
    (hp : Prime p) (large : 5≤p) (root : r^2=2) (vfn : w.deep 1 fn) (van : w.deep 1 an) :
    o.place.residue.map s.primary.x=0 ∧ o.place.residue.map s.alternate.x=0 := by
  have D:=(curve_coeffs w hp large root).2.2
  have D':=(curve_coeffs w hp large (show (-r)^2=2 by grobner)).2.2
  exact ⟨o.residueZero _ (parameterDepth hp D s.firstChart.numerator (s.firstChart.numValue ▸ vfn) (by decide) (by decide)),
         o.residueZero _ (parameterDepth hp D' s.secondChart.numerator (s.secondChart.numValue ▸ van) (by decide) (by decide))⟩

theorem RowGeometry.ratioValue (s : RowGeometry o short m n r L A fn fr an ar) (l : o.O)
    (eq : ratio s.primary l) : o.incl.map l=L := by
  have nz : o.incl.map s.primary.y≠0 := s.firstChart.reference.live.2.2
  obtain ⟨inv,iu⟩:=s.primary.ry_unit
  have nz' : o.incl.map s.primary.ry≠0 := by
    intro z
    have e:=congrArg o.incl.map iu
    rw [o.incl.mul,z,Semiring.mul_zero,o.incl.one] at e
    exact Field.zero_ne_one e
  have both:=(w.product nz nz').1
  have mul:=congrArg o.incl.map eq
  unfold ratio at eq
  change o.incl.map ((s.primary.y*s.primary.ry)*l)=o.incl.map (s.primary.x*s.primary.nx) at mul
  rw [o.incl.mul,s.firstRatio,o.incl.mul] at mul
  have killed : (o.incl.map s.primary.y*o.incl.map s.primary.ry)*(o.incl.map l-L)=0 := by grobner
  have d:=(Field.of_mul_eq_zero killed).resolve_left both
  grobner

end ProjectionFibres.Comparison
