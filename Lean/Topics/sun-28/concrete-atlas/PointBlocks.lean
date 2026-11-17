import OrdinateBlocks
import TracePoints
import FixedSoundness

/-! The input slot, the nine doubles, exceptional-point guards and the odd tests. -/
namespace Sun28.Concrete
open Sun28.GroupCharts Sun28.TraceAtlas Sun28.WitnessIndices Sun28.Ordinates ZInQ
noncomputable section
variable {R α : Type*} [CommRing R] {n : ℕ}

def sequence : {n : ℕ} → (Fin n → Program R α) → Program R (Fin n → α)
  | 0,_ => .pure Fin.elim0
  | n+1,f => Program.bind (fun a => Program.bind (fun tail => .pure (Fin.cons a tail))
      (sequence (n:=n) (Fin.tail f))) (f 0)

theorem eval_sequence (φ : R →+* ℚ) (f : Fin n → Program R α) :
    Program.eval φ (sequence f) = fun i => Program.eval φ (f i) := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp only [sequence,Program.eval_bind,Program.eval,
      ih,Fin.cons_zero,Fin.cons_succ,Fin.tail]

def doublesCode (v : Fin 9 → PointCode R) := sequence fun i => PointCode.mulProgram 2 (v i)

theorem doubles_inputs (φ : R →+* ℚ) (v : Fin 9 → PointCode R) (a : Fin 9 → AffineInput)
    (hp : ∀ i, GroupCharts.Represents φ (v i) (a i).point) :
    Inputs φ (fromNine (Program.eval φ (doublesCode v))) (nineAffine a).doubles := by
  rw [doublesCode,eval_sequence]
  refine ⟨PointCode.mul_correct φ 2 (hp 0),PointCode.mul_correct φ 2 (hp 1),PointCode.mul_correct φ 2 (hp 2),
    PointCode.mul_correct φ 2 (hp 3),PointCode.mul_correct φ 2 (hp 4),fun i => PointCode.mul_correct φ 2 (hp _)⟩

def inputPoly (i : Fin 28) : NineRing := MvPolynomial.C (MvPolynomial.X i)
def inputExpr (i : Fin 28) : E NineRing := .pure (.ofPair (inputPoly i) 0)

theorem input_spec (p : Fin 28 → ℚ) (t : Fin 9 → ℚ) (i : Fin 28) :
    RatValue (ev (Sun28.Branches.value p) t) (inputExpr i) (p i) := by
  refine ⟨Quad.good_pair _ _ _,?_⟩
  ext <;> simp [Program.eval,inputExpr,inputPoly,Quad.eval,Quad.ofPair,Sun28.Branches.value,ev]

def pointBlocks (c : ℤ) (v : Codes R) : Program R (Fin 4 → TestBlock R) :=
  Program.bind (fun z => .pure
    ![TestBlock.tests [] [PointCode.equalTest v.q .infinity,PointCode.equalTest v.h .infinity,
        PointCode.equalTest z .infinity],pointOdd v.n,pointOdd v.t,pointOdd v.z])
    (PointCode.translate c v.h PointCode.generator)

theorem point_blocks_spec (φ : R →+* ℚ) {v : Codes R} {w : NinePoints} (hv : Inputs φ v w) (c : ℤ) :
    (∀ i, ((Program.eval φ (pointBlocks c v)) i).Valid φ) ↔
      w.Q≠0 ∧ w.H≠0 ∧ translatedBase w c≠0 ∧ RationalOddChart w.N ∧ RationalOddChart w.T ∧ RationalOddChart w.Z := by
  let z := Program.eval φ (PointCode.translate c v.h PointCode.generator)
  have hz : GroupCharts.Represents φ z (translatedBase w c) :=
    PointCode.translate_correct φ c hv.h (PointCode.generator_correct φ)
  have he : GroupCharts.Represents φ (.infinity : PointCode R) (0:CPoint) := .infinity
  have guards : (TestBlock.tests [] [PointCode.equalTest v.q .infinity,PointCode.equalTest v.h .infinity,
      PointCode.equalTest z .infinity]).Valid φ ↔ w.Q≠0 ∧ w.H≠0 ∧ translatedBase w c≠0 := by
    simp [TestBlock.Valid,PointCode.equalTest_correct φ hv.q he,PointCode.equalTest_correct φ hv.h he,
      PointCode.equalTest_correct φ hz he]
  have hn := point_odd_valid φ hv.n
  have ht := point_odd_valid φ hv.t
  have hu := point_odd_valid φ hv.z
  constructor
  · intro h
    simp only [pointBlocks,Program.eval_bind,Program.eval] at h
    obtain ⟨a,b,c'⟩ := guards.mp (h 0)
    exact ⟨a,b,c',hn.mp (h 1),ht.mp (h 2),hu.mp (h 3)⟩
  · rintro ⟨a,b,c',n,t,u⟩ i
    simp only [pointBlocks,Program.eval_bind,Program.eval]
    fin_cases i <;> first | exact guards.mpr ⟨a,b,c'⟩ | exact hn.mpr n | exact ht.mpr t | exact hu.mpr u

end
end Sun28.Concrete
#print axioms Sun28.Concrete.eval_sequence
#print axioms Sun28.Concrete.doubles_inputs
#print axioms Sun28.Concrete.input_spec
#print axioms Sun28.Concrete.point_blocks_spec
