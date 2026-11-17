import RationalChart
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
def halfSlots := [143,155,167]
def oneSlots := [80,90,96,102,191,193,195,197,199,201,203,205,207,209,211,213,215,217,219,221,223,225]

def integralValues (i : Nat) : Int :=
  if i=178 then 197769848042768400000000 else
  if i=179 then 1529819947298299936610017206298061877288175236769780537806873600000000000000000000000000000000 else
  if oneSlots.contains i then 1 else 0


def markTest (p : Pivot) := decide (intVal integralValues p.row=0)
end PhysicalProjection
