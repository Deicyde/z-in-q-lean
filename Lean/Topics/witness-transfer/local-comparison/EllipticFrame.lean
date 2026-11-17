import JetEvaluation
import ContactFrame

namespace WitnessTransfer.Local
open Lean.Grind FiniteJet IndependentIndices IndependentIndices.ChartJets
attribute [local instance] Semiring.natCast Ring.intCast

variable {O K : Type} [CommRing O] [Field K] [IsCharP K 0]

/-- Concrete evaluations of both rational reference charts at the same point. -/
structure MixedRef (h : RingMap O K) (y pade short : O) where
  curve : CurveData K 12
  p : J O 13
  s : J O 13
  pChart : val curve.w pDenom*(h.jet 13 p)=X 13*val curve.w pNumer
  sChart : val curve.w [15]*(h.jet 13 s)=X 13*val curve.w IndependentIndices.ChartJets.short
  pValue : expands 13 y pade p
  sValue : expands 13 y short s

theorem MixedRef.difference {h : RingMap O K} (inj : Function.Injective h.map)
    {y p s} (ref : MixedRef h y p s) : ∃ c : O,s-p=y^13*c := by
  have eq:=mixed_at_thirteen rfl ref.curve (h.jet 13 ref.p) (h.jet 13 ref.s) ref.pChart ref.sChart
  have same : ref.p=ref.s := h.jet_inj inj 13 eq
  obtain ⟨a,ha⟩:=ref.pValue
  obtain ⟨b,hb⟩:=ref.sValue
  have eqv := congrArg (horner y 13) same
  exact ⟨b-a,by grobner⟩

inductive RefLaw (h : RingMap O K) (y target value : O) : Parameter → Type
  | same {c} : value=target → RefLaw h y target value c
  | mixed : MixedRef h y target value → RefLaw h y target value .short

structure JoinedPair (h : RingMap O K) (c : Parameter) (s : Side O) (m a : Int) where
  commonValue : O
  refValue : O
  numerator : SourceValue O K h c m s.x (s.x*s.nx) commonValue
  reference : SourceValue O K h c a s.y refValue commonValue
  refChart : RefLaw h s.y (s.y*s.ry) refValue c

theorem JoinedPair.absolute {h : RingMap O K} (inj : Function.Injective h.map)
    {c s m a} (p : JoinedPair h c s m a) : Nonempty (AtMultiple s m a (4*c.k)) := by
  have newRef : ∃ r : O,p.refValue=s.y*s.ry+s.y^(4*c.k+1)*r := by
    cases p.refChart with
    | same eq => exact ⟨0,by rw [eq];grobner⟩
    | mixed e =>
      obtain ⟨r,hr⟩:=e.difference inj
      exact ⟨r,by change _=s.y*s.ry+s.y^13*r;grobner⟩
  obtain ⟨r,hr⟩:=newRef
  refine ⟨⟨p.commonValue,r,p.numerator.absolute inj,?_⟩⟩
  rw [← hr]
  exact p.reference.absolute inj

theorem value_tangent {h : RingMap O K} (inj : Function.Injective h.map)
    {c b z v vb} (x : SourceValue O K h c b z v vb) :
    ∃ r : O,x.multiplierTail=(b:O)+z*r := by
  obtain ⟨r,hr⟩:=x.evaluatesMultiplier
  have c0 : x.m.1=(b:O) := inj (x.tangent.trans (h.int b).symm)
  refine ⟨horner z (4*c.k) x.m.2+z^(4*c.k)*r,?_⟩
  change x.multiplierTail=x.m.1+z*horner z (4*c.k) x.m.2+z^(4*c.k+1)*r at hr
  rw [c0,Semiring.pow_succ] at hr
  grobner

theorem JoinedPair.tangent {h : RingMap O K} (inj : Function.Injective h.map)
    {c s m a} (pair : JoinedPair h c s m a)
    (samePoint : s.x*pair.numerator.multiplierTail=s.y*pair.reference.multiplierTail) :
    Nonempty (Tangent s m a) := by
  obtain ⟨rx,hx⟩:=value_tangent inj pair.numerator
  obtain ⟨ry,hy⟩:=value_tangent inj pair.reference
  exact ⟨⟨rx,ry,by rwa [hx,hy] at samePoint⟩⟩

def altChart (short : Bool) : Parameter := if short then .short else .pade

/-- The two actual group identities are represented by common evaluation values
and by their first-order parameter expansions. -/
structure PhysicalRow (h : RingMap O K) (p : Nat) (short : Bool) (m n : Int) where
  primary : Side O
  alternate : Side O
  u : Int
  firstPair : JoinedPair h .raw primary m (2*u)
  secondPair : JoinedPair h (altChart short) alternate (m-2) (2*(u-n))
  firstPoint : primary.x*firstPair.numerator.multiplierTail=primary.y*firstPair.reference.multiplierTail
  secondPoint : alternate.x*secondPair.numerator.multiplierTail=alternate.y*secondPair.reference.multiplierTail
  firstDepth : ∃ v : O,primary.y=(p:O)^20*v
  secondDepth : ∃ v : O,alternate.y=(p:O)^1*v
  crossError : O
  cross : crossEq primary alternate ((p:O)^(precision short)*crossError)

private noncomputable def PhysicalRow.observation {h : RingMap O K} (inj : Function.Injective h.map)
    {p short m n} (d : PhysicalRow h p short m n) : Observation O p short m n :=
  ⟨d.primary,d.alternate,d.u,Classical.choice (d.firstPair.tangent inj d.firstPoint),
     Classical.choice (d.secondPair.tangent inj d.secondPoint),
     Classical.choice (d.firstPair.absolute inj),
     (show 4*(altChart short).k=alternateOrder short from by cases short <;> rfl) ▸
        Classical.choice (d.secondPair.absolute inj),d.firstDepth,d.secondDepth,d.crossError,d.cross⟩

structure PrimeInputs (p : Nat) (m : Int) (ns : Labels) (B : Rat) where
  integers : Type
  coeffs : Type
  residue : Type
  [integersRing : CommRing integers]
  [coefficientField : Field coeffs]
  [characteristic : IsCharP coeffs 0]
  [residueField : Field residue]
  incl : RingMap integers coeffs
  injective : Function.Injective incl.map
  place : Place integers residue
  odd : p%2=1
  ten : Residue (p^10)
  forty : Residue (p^40)
  red10 : @RingMap integers ten.carrier _ ten.ring
  red40 : @RingMap integers forty.carrier _ forty.ring
  a : PhysicalRow incl p true m ns.n₁
  b : PhysicalRow incl p false m ns.n₂
  c : PhysicalRow incl p false m ns.n₃
  d : PhysicalRow incl p false m ns.n₄
  za : place.residue.map a.primary.x=0 ∧ place.residue.map a.alternate.x=0
  zb : place.residue.map b.primary.x=0 ∧ place.residue.map b.alternate.x=0
  zc : place.residue.map c.primary.x=0 ∧ place.residue.map c.alternate.x=0
  zd : place.residue.map d.primary.x=0 ∧ place.residue.map d.alternate.x=0
  detector : letI:=ten.ring;∀ l,ratio a.primary l → (B.den:ten.carrier)*red10.map l=(B.num:ten.carrier)
  lucasTest : letI:=forty.ring;∀ x y z,ratio b.primary x → ratio c.primary y → ratio d.primary z →
    IndependentIndices.lucas (red40.map x) (red40.map y) (red40.map z)=0

theorem PrimeInputs.contact {p m ns B} (a : PrimeInputs p m ns B) : Nonempty (Contact p m ns B) := by
  letI := a.integersRing
  letI := a.coefficientField
  letI := a.characteristic
  letI := a.residueField
  exact observed_contact p m ns B a.odd a.place a.ten a.forty a.red10 a.red40
    (a.a.observation a.injective) (a.b.observation a.injective)
    (a.c.observation a.injective) (a.d.observation a.injective) a.za a.zb a.zc a.zd a.detector a.lucasTest

/-- The released Frame, with its actual chosen multiplier and list of observed
primes, including an empty list. -/
def physical_frame {m : Int} {ns : Labels} {B : Rat} (ps : List Nat)
    (atPrime : ∀ p∈ps,Nonempty (PrimeInputs p m ns B)) : Frame ns B :=
  ⟨m,ps,fun p hp=>(atPrime p hp).elim (fun d=>d.contact)⟩

theorem physical_defects {m : Int} {ns : Labels} {B : Rat} (ps : List Nat)
    (atPrime : ∀ p∈ps,Nonempty (PrimeInputs p m ns B)) : Defects (radical ps) ns B :=
  (physical_frame ps atPrime).defects

#print axioms MixedRef.difference
#print axioms JoinedPair.absolute
#print axioms PrimeInputs.contact
#print axioms physical_frame
#print axioms physical_defects
end WitnessTransfer.Local
