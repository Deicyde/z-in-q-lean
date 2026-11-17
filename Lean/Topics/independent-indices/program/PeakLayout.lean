import IndexLayout
namespace IndependentIndices
open Data

/-- Only the first local variable may receive the distinguished input. Inspect
    the tail once to establish this property of a protected route. -/
def peakOK (rs : Routes) (r : Ref) : Bool :=
  r.origin && ((rs[r.cell]!).slots.toList.drop 1).all (fun j=>decide (j≠1))

set_option maxRecDepth 6000 in
private theorem parent_peak : oldShape.high.refs.all (peakOK oldRoutes)=true := by decide +kernel
set_option maxRecDepth 6000 in
private theorem split_peak : newShape.high.refs.all (peakOK newRoutes)=true := by decide +kernel

theorem peak_routes : oldShape.high.refs.all (peakOK oldRoutes)=true ∧
    newShape.high.refs.all (peakOK newRoutes)=true := ⟨parent_peak,split_peak⟩

end IndependentIndices
