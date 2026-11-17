import PairResidues

namespace Prime23.Base
open PhysicalProjection.Comparison StructuralReduction

def xP : Q2 := (57/8,-7/2)
def yP : Q2 := (-165/8,417/32)
def D : Q2 := (11,-6)
def qP := inverse xP
def doubleRoot := times (scale 2 yP) (inverse (plus (sq xP) D))
def tangent := times (plus (scale 3 (sq xP)) (scale (-1) D)) (inverse (scale 2 yP))
def xDouble := plus (sq tangent) (scale (-2) xP)
def qDouble := inverse xDouble

theorem reciprocal_values :
    qP=(456/1681,224/1681) ∧
    doubleRoot=(-2645904/4905889,-231612/4905889) ∧
    qDouble=(7108096214304/24067746880321,1225646234496/24067746880321) ∧
    times xP qP=(1,0) ∧ times xDouble qDouble=(1,0) ∧ qDouble=sq doubleRoot := by
  decide +kernel

theorem dyadic :
    PairRed 2 (scale (1/8) qP) (1,0) ∧
    order 2 (norm qP)=6 ∧ order 2 (norm xP)= -6 := by
  refine ⟨⟨⟨57,1681,by decide +kernel,by decide +kernel,by decide +kernel⟩,
    ⟨28,1681,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩,?_⟩
  decide +kernel

theorem curve_reduction :
    PairRed 3 xP (0,1) ∧ PairRed 3 (scale (1/3) yP) (1,2) ∧ PairRed 3 D (2,0) := by
  refine ⟨⟨⟨114,16,?_,?_,?_⟩,⟨-14,4,?_,?_,?_⟩⟩,
    ⟨⟨-110,16,?_,?_,?_⟩,⟨278,64,?_,?_,?_⟩⟩,⟨⟨11,1,?_,?_,?_⟩,⟨-6,1,?_,?_,?_⟩⟩⟩
  all_goals decide +kernel

theorem triadic :
    PairRed 3 (scale (1/3) doubleRoot) (2,1) ∧
    PairRed 3 (scale (1/9) qDouble) (0,1) ∧ order 3 (norm qDouble)=4 := by
  have r : PairRed 3 (scale (1/3) doubleRoot) (2,1) :=
    ⟨⟨-881968,4905889,by decide +kernel,by decide +kernel,by decide +kernel⟩,
     ⟨-77204,4905889,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩
  have e : scale (1/9) qDouble=times (scale (1/3) doubleRoot) (scale (1/3) doubleRoot) :=
    by decide +kernel
  exact ⟨r,e ▸ (show PairRed 3 _ (0,1) from (show mulR ((2,1):Residues 3) (2,1)=(0,1) by
    decide +kernel) ▸ r.mul r),by decide +kernel⟩

#print axioms reciprocal_values
#print axioms dyadic
#print axioms curve_reduction
#print axioms triadic
end Prime23.Base
