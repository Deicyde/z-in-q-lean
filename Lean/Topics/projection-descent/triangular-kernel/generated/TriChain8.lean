import TriChain7
open ZeroInput.Sparse ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem slots0 (g : Bool) : slots (tail0 g)=[120,121,189,175,188,190,197,198,186,187,199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p205.slot :: slots (tail1 g)=_; rw [slots1]; cases g <;> rfl
theorem good0 (g : Bool) : valid (tail0 g)=true := by
  change (decide (p205.lead≠0 ∧ p205.slot∉slots (tail1 g)) && reads (apart (p205.slot::slots (tail1 g))) p205.num && valid (tail1 g))=true
  rw [slots1,good1]; cases g <;> decide
theorem zero0 (g : Bool) : (tail0 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p205.row=0) && (tail1 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero1]; cases g <;> decide
end Triangular.Data
