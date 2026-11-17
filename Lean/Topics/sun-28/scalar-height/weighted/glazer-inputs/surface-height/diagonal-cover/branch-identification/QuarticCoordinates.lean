import JacobianTwists
import Mathlib.Tactic

namespace ZInQBlueprint.BranchId
open Diagonal210
noncomputable section
set_option maxRecDepth 10000

/-- The three columns remaining when the row's inertia label is omitted. -/
def keep : Fin 4 → Fin 3 → Fin 4 := ![![1,2,3],![0,2,3],![0,1,3],![0,1,2]]
def numeratorCoeffs : Fin 4 → Fin 5 → ℚ :=
  ![![-343,4802,-22295,28812,-12348],![-343,-2744,-3430,8232,-3087],![-343,0,-686,0,-343],![-343,-686,-1715,-1372,-1372]]

def forwardCoeffs : Fin 4 → Fin 3 → Fin 3 → ℚ :=
  ![![![30,-240,180],![1470,0,-8820],![(735/4),(-2205/4),(2205/2)]],![![49,196,-147],![1470,-4410,-4410],![(735/4),0,(2205/4)]],![![49,0,49],![30,30,-30],![(735/4),-735,(-735/4)]],![![49,49,98],![30,0,-60],![1470,11760,2940]]]

def inverseCoeffs : Fin 4 → Fin 3 → Fin 3 → ℚ :=
  ![![![(-1/100),(1/2940),(16/3675)],![(-1/150),0,(4/3675)],![(-1/600),(-1/17640),(8/11025)]],![![(3/686),(1/5145),(2/735)],![(1/343),(-1/10290),0],![(-1/686),(-1/15435),(2/2205)]],![![(1/98),(1/75),(2/3675)],![0,(1/150),(-4/3675)],![(1/98),(-1/75),(-2/3675)]],![![(4/343),(1/60),(-1/20580)],![(-1/343),0,(1/10290)],![(2/343),(-1/120),(-1/41160)]]]

variable {K : Type*} [Field K] [CharZero K]

def form4 (v : Fin 5 → ℚ) (x : K) : K :=
  v 0*x^4+v 1*x^3+v 2*x^2+v 3*x+v 4

/-- The polynomial on the right of the equation printed in Table 2. -/
def published (i : Fin 4) (x : K) := form4 (dataRow i) x

def numerator (i : Fin 4) (x : K) := form4 (numeratorCoeffs i) x

def lin (v : Fin 3 → ℚ) (z : Fin 3 → K) : K := v 0*z 0+v 1*z 1+v 2*z 2

def quad (i : Fin 4) (j : Fin 3) (x : K) := lin (forwardCoeffs i j) ![x^2,x,1]

def readout (i : Fin 4) (k : Fin 3) (z : Fin 3 → K) := lin (inverseCoeffs i k) z

/-- Twelve literal identities for the quartics, all over the same marked s-line. -/
theorem covariants (i : Fin 4) (j : Fin 3) (x : K) :
    quad i j x ^ 2 = coefficient (keep i j) *
      (numerator i x - mark (keep i j)*published i x) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [quad,lin,forwardCoeffs,numerator,numeratorCoeffs,published,form4,dataRow,mark,coefficient,keep] <;> ring

/-- The inverse coefficient matrix recovers the three original homogeneous monomials. -/
theorem inverse_times_forward (i : Fin 4) (v : Fin 3 → K) (k : Fin 3) :
    readout i k (fun j => lin (forwardCoeffs i j) v) = v k := by
  fin_cases i <;> fin_cases k <;>
    norm_num [readout,lin,forwardCoeffs,inverseCoeffs] <;> ring

theorem forward_times_inverse (i : Fin 4) (j : Fin 3) (z : Fin 3 → K) :
    lin (forwardCoeffs i j) (fun k => readout i k z) = z j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [readout,lin,forwardCoeffs,inverseCoeffs] <;> ring

def omitted (i : Fin 4) (s : K) (z : Fin 3 → K) : Prop :=
  ∀ j,z j ^ 2 = coefficient (keep i j) * (s-mark (keep i j))

theorem parametrizing_conic {i : Fin 4} {s : K} {z : Fin 3 → K} (hit : omitted i s z) :
    readout i 0 z*readout i 2 z=(readout i 1 z)^2 := by
  have h0:=hit 0; have h1:=hit 1; have h2:=hit 2
  fin_cases i <;>
    norm_num [keep,mark,coefficient,readout,lin,inverseCoeffs] at h0 h1 h2 ⊢
  · linear_combination ((-1/36000))*h0 + ((-1/51861600))*h1 + ((16/8103375))*h2
  · linear_combination ((-1/67228))*h0 + ((-1/45378900))*h1 + ((4/1620675))*h2
  · linear_combination ((1/9604))*h0 + ((-1/4500))*h1 + ((-4/2701125))*h2
  · linear_combination ((1/16807))*h0 + ((-1/7200))*h1 + ((-1/121010400))*h2

end
end ZInQBlueprint.BranchId
#print axioms ZInQBlueprint.BranchId.covariants
#print axioms ZInQBlueprint.BranchId.inverse_times_forward
#print axioms ZInQBlueprint.BranchId.forward_times_inverse
#print axioms ZInQBlueprint.BranchId.parametrizing_conic
