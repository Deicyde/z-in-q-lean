import WitnessCoordinates
import LogarithmicResidual

namespace Sun28.FiveDescent.ResidueField
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres.Sharp Sun28.HeightExtension
open Sun28.HeightBudget Sun28.MinimalConductors Sun28.HeightCubics.Refinement

theorem logarithmic_iff_fieldHeight (units:PublishedCorollary72) (pell:PublishedAllPell)
    (classes:PublishedClassRegulator) (formula:QuadraticCharacterDiscriminants)
    (pub:PublishedElliptic) :
    Sun28.HeightCubics.Pooled.Logarithmic.Remaining ↔ FieldHeight glazerConstant24 :=
  (Sun28.HeightCubics.Pooled.Logarithmic.original_iff_logarithmic units pell classes formula pub).symm.trans
    (original_iff_fieldHeight _)

end Sun28.FiveDescent.ResidueField
#print axioms Sun28.FiveDescent.ResidueField.logarithmic_iff_fieldHeight
