import ZInQKernel.Contrib.HDecomp.LeafPush2.R22
import ThetaConvergence

namespace ZInQBlueprint.OriginalTheta
open Complex ThetaPeriod ZInQ.LeafPush2
noncomputable section

/-- Encode the first half-characteristic in the two high bits, and the
second in the two low bits, in the order of the two lattice coordinates. -/
def bit (j : Fin 16) (k : ℕ) : Fin 2 := ⟨j.val / 2^k % 2,Nat.mod_lt _ (by decide)⟩

def characteristic (j : Fin 16) : Char2 :=
  (![bit j 2,bit j 3],![bit j 0,bit j 1])

def number (m : Char2) : Fin 16 :=
  ⟨m.2 0 + 2*(m.2 1 : ℕ)+4*(m.1 0 : ℕ)+8*(m.1 1 : ℕ),by
    have h0 := (m.2 0).isLt;have h1 := (m.2 1).isLt
    have h2 := (m.1 0).isLt;have h3 := (m.1 1).isLt;omega⟩

def characteristicEquiv : Fin 16 ≃ Char2 where
  toFun := characteristic
  invFun := number
  left_inv := by decide
  right_inv := by decide

def lattice : (Fin 2 → ℤ) ≃ ℤ × ℤ where
  toFun n := (n 0,n 1)
  invFun v := ![v.1,v.2]
  left_inv n := by ext i;fin_cases i <;> rfl
  right_inv v := by cases v;rfl

def omega (Z : SiegelPeriod) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Z.z11,Z.z12; Z.z12,Z.z22]

/-- The actual PR114 summand, before taking its sum over the lattice. -/
def originalTerm (Ω : Matrix (Fin 2) (Fin 2) ℂ) (m : Char2) (n : Fin 2 → ℤ) : ℂ :=
  Complex.exp (Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ
          Ω.mulVec (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2)) +
      2 * Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ (fun i => ((m.2 i : ℕ) : ℂ) / 2)))

theorem term_eq (Z : SiegelPeriod) (j : Fin 16) (n : Fin 2 → ℤ) :
    originalTerm (omega Z) (characteristic j) n = term Z j (lattice n) := by
  unfold originalTerm term
  congr 1
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,omega,characteristic,lattice,bit,halfBit]
  ring

/-- Exact equality with Glazer's theta constant, including odd coordinates. -/
theorem thetaConst_eq (Z : SiegelPeriod) (j : Fin 16) :
    thetaConst (omega Z) (characteristic j) = thetaNull Z j := by
  change (∑' n : Fin 2 → ℤ, originalTerm (omega Z) (characteristic j) n) = _
  simp_rw [term_eq]
  exact lattice.tsum_eq (term Z j)

theorem original_summable_norm (Z : SiegelPeriod) (m : Char2) :
    Summable (fun n => ‖originalTerm (omega Z) m n‖) := by
  obtain ⟨j,rfl⟩ := characteristicEquiv.surjective m
  change Summable (fun n => ‖originalTerm (omega Z) (characteristic j) n‖)
  simp_rw [term_eq]
  exact lattice.summable_iff.mpr (summable_norm_terms Z j)

theorem omega_isSiegel (Z : SiegelPeriod) : IsSiegel (omega Z) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · intro v vn
      obtain ⟨t,tp,bound⟩ := gaussian_lower Z
      specialize bound (v 0) (v 1)
      change t*((v 0)^2+(v 1)^2) ≤ Z.z11.im*(v 0)^2+2*Z.z12.im*(v 0)*(v 1)+Z.z22.im*(v 1)^2 at bound
      have sum : 0 < (v 0)^2+(v 1)^2 := by
        by_contra! h
        have n0 : v 0=0 := by nlinarith [sq_nonneg (v 1),sq_nonneg (v 0)]
        have n1 : v 1=0 := by nlinarith [sq_nonneg (v 1),sq_nonneg (v 0)]
        apply vn
        ext i
        fin_cases i <;> assumption
      have lt := lt_of_lt_of_le (mul_pos tp sum) bound
      simpa [omega,Matrix.mulVec,dotProduct,Fin.sum_univ_two,pow_two,mul_add,add_mul] using (by
        linear_combination lt : 0<v 0*(Z.z11.im*v 0+Z.z12.im*v 1)+v 1*(Z.z12.im*v 0+Z.z22.im*v 1))

/-- Every PR114 Siegel matrix also supplies our Sylvester-minor record. -/
def periodOf (Ω : Matrix (Fin 2) (Fin 2) ℂ) (h : IsSiegel Ω) : SiegelPeriod where
  z11 := Ω 0 0
  z12 := Ω 0 1
  z22 := Ω 1 1
  im11 := h.2.diag_pos
  imdet := by
    have hs : Ω 1 0 = Ω 0 1 := congrFun (congrFun h.1 0) 1
    simpa only [Matrix.det_fin_two,Matrix.map_apply,hs,pow_two] using h.2.det_pos

theorem omega_periodOf (Ω : Matrix (Fin 2) (Fin 2) ℂ) (h : IsSiegel Ω) : omega (periodOf Ω h)=Ω := by
  have hs : Ω 1 0 = Ω 0 1 := congrFun (congrFun h.1 0) 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omega,periodOf,hs]

end
end ZInQBlueprint.OriginalTheta
#print axioms ZInQBlueprint.OriginalTheta.characteristicEquiv
#print axioms ZInQBlueprint.OriginalTheta.term_eq
#print axioms ZInQBlueprint.OriginalTheta.thetaConst_eq
#print axioms ZInQBlueprint.OriginalTheta.original_summable_norm
#print axioms ZInQBlueprint.OriginalTheta.omega_isSiegel
#print axioms ZInQBlueprint.OriginalTheta.omega_periodOf
