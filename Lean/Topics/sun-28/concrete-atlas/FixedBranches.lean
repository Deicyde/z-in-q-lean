import PointBlocks
import TracePacket
import FreeParameters
import ScaledConductor

/-! The complete finite branch list on the 28 specified base coordinates. -/
namespace Sun28.Concrete
open GroupCharts TraceAtlas WitnessIndices ScalarHeight Ordinary Forward FixedPreparation ZInQ
noncomputable section

def eIndex (j : Fin 3) : Fin 28 := ((⟨19+2*j.val,by omega⟩ : Fin 27).succ)
def zIndex (j : Fin 3) : Fin 28 := ((⟨20+2*j.val,by omega⟩ : Fin 27).succ)

def poleBlock (q : NineRing × NineRing) (e z : Fin 28) : TestBlock NineRing :=
  .pole ⟨q.1,q.2,inputPoly e,inputPoly z⟩

def packetBlocks (o : Packet NineRing) : Fin 5 → TestBlock NineRing :=
  Fin.cons (.tests [] o.guards) (Fin.snoc (fun i => poleBlock (o.ordinary i) (eIndex i) (zIndex i))
    (poleBlock o.scalar 26 27))

private theorem pole_block_valid (p : Fin 28 → ℚ) (t : Fin 9 → ℚ) (q : NineRing × NineRing)
    (e z : Fin 28) (B : ℚ) (hq : ev (Branches.value p) t q.2≠0 ∧ val (ev (Branches.value p) t) q=B) :
    (poleBlock q e z).Valid (ev (Branches.value p) t) ↔ poleAt smallMultipliers B (p e) (p z) := by
  dsimp only [poleBlock,TestBlock.Valid]
  rw [show ev (Branches.value p) t q.1 / ev (Branches.value p) t q.2=B from hq.2]
  rw [and_iff_right hq.1]
  simp [inputPoly,ev,Branches.value]

def fixedPacket (v : Codes NineRing) (pos : Bool) :=
  packet v fixedMultiplier anchor (inputExpr 0) (inputExpr 19)
    (TraceAtlas.rat (gamma:ℚ)) denominator pos

def signTests (w : NinePoints) (p : Fin 28 → ℚ) (pos : Bool) : Prop :=
  let M := fixedMultiplier
  let β := beta (p 0)
  let r := scalarRadicand β
  let W := scalarTree r (scalarEntries w M)
  (∀ j, side (pointScale w M j) (p 19)) ∧
    (∀ j, let s := pointScale w M j
      ordinaryAtPair w M anchor β (s^2) (s^2*p 19) smallMultipliers (p (eIndex j)) (p (zIndex j))) ∧
    W≠0 ∧ poleAt smallMultipliers (signedValue r (sign pos) gamma denominator W) (p 26) (p 27)

theorem packet_blocks_spec (p : Fin 28 → ℚ) (t : Fin 9 → ℚ) {v : Codes NineRing} {w : NinePoints}
    (h : Inputs (ev (Branches.value p) t) v w) (pos : Bool) :
    (∀ i, (packetBlocks (Program.eval (ev (Branches.value p) t) (fixedPacket v pos)) i).Valid
      (ev (Branches.value p) t)) ↔ signTests w p pos := by
  let φ := ev (Branches.value p) t
  let o := Program.eval φ (fixedPacket v pos)
  have spec : PacketSpec φ o w fixedMultiplier anchor (p 0) (p 19) gamma denominator pos :=
    packet_spec h _ _ (input_spec p t 0) (input_spec p t 19) (lit_spec φ _) _ _
  let M := fixedMultiplier
  let β := beta (p 0)
  let r := scalarRadicand β
  let T := scalarTree r (scalarEntries w M)
  have first j := pole_block_valid p t (o.ordinary j) (eIndex j) (zIndex j) _ (spec.ordinary j)
  have last := pole_block_valid p t o.scalar 26 27 _ spec.scalar
  have head : (packetBlocks o 0).Valid φ ↔ TraceAtlas.Guards φ o.guards := by
    change ((_ ) ∧ _) ↔ _
    exact ⟨fun v => v.2,fun v => ⟨by simp,v⟩⟩
  constructor
  · intro all
    obtain ⟨ordinary,scalar⟩ := spec.guards.1 (head.1 (all 0))
    refine ⟨fun j => (ordinary j).1,fun j => ⟨(ordinary j).2,?_⟩,scalar,last.1 ?_⟩
    · apply (first j).1
      simpa only [packetBlocks,Fin.cons_succ,Fin.snoc_castSucc] using all j.castSucc.succ
    · simpa only [packetBlocks,Fin.cons_succ,Fin.snoc_last] using all (Fin.last 3).succ
  · rintro ⟨side,ord,tree,sc⟩
    refine Fin.cases (head.2 (spec.guards.2 ⟨fun j => ⟨side j,(ord j).1⟩,tree⟩)) ?_
    refine Fin.lastCases ?_ (fun j => ?_)
    · simpa only [packetBlocks,Fin.cons_succ,Fin.snoc_last] using last.2 sc
    · simpa only [packetBlocks,Fin.cons_succ,Fin.snoc_castSucc] using (first j).2 (ord j).2

def sideData (w : NinePoints) : Prop :=
  w.Q≠0 ∧ w.H≠0 ∧ translatedBase w anchor≠0 ∧ RationalOddChart w.N ∧ RationalOddChart w.T ∧ RationalOddChart w.Z

def branchProgram (pos : Bool) (v : Fin 9 → PointCode NineRing) : Program NineRing (Fin 9 → TestBlock NineRing) :=
  Program.bind (fun d => Program.bind (fun g => Program.bind (fun o => .pure (Fin.append g (packetBlocks o)))
      (fixedPacket (fromNine d) pos)) (pointBlocks anchor (fromNine d))) (doublesCode v)

private theorem append_valid {a b : ℕ} {R : Type*} [CommRing R] (φ : R →+* ℚ)
    (l : Fin a → TestBlock R) (r : Fin b → TestBlock R) :
    (∀ i, (Fin.append l r i).Valid φ) ↔ (∀ i, (l i).Valid φ) ∧ ∀ i, (r i).Valid φ := by
  constructor
  · intro h
    exact ⟨fun i => by simpa only [Fin.append_left] using h (Fin.castAdd b i),
      fun i => by simpa only [Fin.append_right] using h (Fin.natAdd a i)⟩
  · rintro ⟨hl,hr⟩ i
    refine Fin.addCases (m:=a) (n:=b) (fun k => ?_) (fun k => ?_) i
    · simpa only [Fin.append_left] using hl k
    · simpa only [Fin.append_right] using hr k

theorem program_spec (p : Fin 28 → ℚ) (t : Fin 9 → ℚ) (v : Fin 9 → PointCode NineRing)
    (a : Fin 9 → AffineInput) (pos : Bool) (hp : ∀ i, GroupCharts.Represents (ev (Branches.value p) t) (v i) (a i).point) :
    (∀ i, ((Program.eval (ev (Branches.value p) t) (branchProgram pos v)) i).Valid (ev (Branches.value p) t)) ↔
      sideData (nineAffine a).doubles ∧ signTests (nineAffine a).doubles p pos := by
  let φ := ev (Branches.value p) t
  have h := doubles_inputs φ v a hp
  rw [← packet_blocks_spec p t h pos]
  unfold sideData
  rw [← point_blocks_spec φ h anchor]
  simp only [branchProgram,Program.eval_bind,Program.eval]
  exact append_valid (a:=4) (b:=5) φ (Program.eval φ (pointBlocks anchor (fromNine (Program.eval φ (doublesCode v))))) (packetBlocks (Program.eval φ (fixedPacket (fromNine (Program.eval φ (doublesCode v))) pos)))

def fixedBranches : List (Compiler.Branch 28) :=
  [false,true].flatMap (fun s => ordinatePanels (branchProgram s))

private theorem sign_relation (p : Fin 28 → ℚ) (a : Fin 9 → AffineInput) (hp : position p a) :
    (∃ s, sideData (nineAffine a).doubles ∧ signTests (nineAffine a).doubles p s) ↔
    FreeTests (fun j => p j.succ) a fixedMultiplier anchor (p 0) gamma denominator smallMultipliers smallMultipliers := by
  let w := (nineAffine a).doubles
  constructor
  · rintro ⟨s,⟨q,h,b,n,t,z⟩,g,ord,tree,pole⟩
    exact ⟨hp,q,h,b,n,t,z,g,ord,sign s,by cases s <;> simp [sign],tree,pole⟩
  · rintro ⟨_,q,h,b,n,t,z,g,ord,δ,hd,tree,pole⟩
    rcases hd with rfl|rfl
    · exact ⟨true,⟨q,h,b,n,t,z⟩,g,ord,tree,pole⟩
    · exact ⟨false,⟨q,h,b,n,t,z⟩,g,ord,tree,pole⟩

set_option maxHeartbeats 800000 in
theorem fixed_exact : ExactBranchList anchor gamma denominator smallMultipliers smallMultipliers fixedBranches := by
  intro p
  change Accepted fixedBranches p ↔ _
  rw [fixedBranches,accepted_flat]
  simp_rw [ordinate_panels_spec (p:=p) (S:=fun a => sideData (nineAffine a).doubles ∧ signTests (nineAffine a).doubles p _)
    (impl:=fun a _ v t h => program_spec p t v a _ h)]
  unfold parameterRelation
  rw [fixed_cutoff,multiplier_at_cutoff]
  constructor
  · rintro ⟨b,_,a,hp,h⟩
    exact ⟨a,(sign_relation p a hp).1 ⟨b,h⟩⟩
  · rintro ⟨a,h⟩
    have hp : position p a := h.1
    obtain ⟨s,hs⟩ := (sign_relation p a hp).2 h
    exact ⟨s,by cases s <;> simp,a,hp,hs⟩

def fixedPolynomial := Branches.polynomial28 (Compiler.branchAtlas fixedBranches)

set_option maxHeartbeats 800000 in
theorem fixed_projection (chart : OrdinaryCharts oldCutoff K0) (units : FiveMarkUnits.PublishedCorollary72)
    (height : FiveMarkTriples.ScaledLargeConductorHeight)
    (integerPoints : IntegerWitnesses anchor gamma denominator smallMultipliers smallMultipliers) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 fixedPolynomial x w=0) ↔ ∃ k : ℤ, x=(k:ℚ) := by
  apply compiled_point_projection anchor_nonzero (by exact_mod_cast gamma_positive.ne')
    (by rwa [fixed_cutoff]) ((FiveMarkTriples.originalFiveHeight_iff_scaled_conductors units).2 height)
    fixedBranches fixed_exact integerPoints x

end
end Sun28.Concrete
#print axioms Sun28.Concrete.packet_blocks_spec
#print axioms Sun28.Concrete.program_spec
#print axioms Sun28.Concrete.fixed_exact
#print axioms Sun28.Concrete.fixed_projection
