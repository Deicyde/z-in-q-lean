import TriChain2
open ZeroInput.Sparse ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem slots45 (g : Bool) : slots (tail45 g)=[208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p626.slot :: slots (tail46 g)=_; rw [slots46]; cases g <;> rfl
theorem good45 (g : Bool) : valid (tail45 g)=true := by
  change (decide (p626.lead≠0 ∧ p626.slot∉slots (tail46 g)) && reads (apart (p626.slot::slots (tail46 g))) p626.num && valid (tail46 g))=true
  rw [slots46,good46]; cases g <;> decide
theorem zero45 (g : Bool) : (tail45 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p626.row=0) && (tail46 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero46]; cases g <;> decide
theorem slots44 (g : Bool) : slots (tail44 g)=[207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p625.slot :: slots (tail45 g)=_; rw [slots45]; cases g <;> rfl
theorem good44 (g : Bool) : valid (tail44 g)=true := by
  change (decide (p625.lead≠0 ∧ p625.slot∉slots (tail45 g)) && reads (apart (p625.slot::slots (tail45 g))) p625.num && valid (tail45 g))=true
  rw [slots45,good45]; cases g <;> decide
theorem zero44 (g : Bool) : (tail44 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p625.row=0) && (tail45 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero45]; cases g <;> decide
theorem slots43 (g : Bool) : slots (tail43 g)=[206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p624.slot :: slots (tail44 g)=_; rw [slots44]; cases g <;> rfl
theorem good43 (g : Bool) : valid (tail43 g)=true := by
  change (decide (p624.lead≠0 ∧ p624.slot∉slots (tail44 g)) && reads (apart (p624.slot::slots (tail44 g))) p624.num && valid (tail44 g))=true
  rw [slots44,good44]; cases g <;> decide
theorem zero43 (g : Bool) : (tail43 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p624.row=0) && (tail44 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero44]; cases g <;> decide
theorem slots42 (g : Bool) : slots (tail42 g)=[205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p623.slot :: slots (tail43 g)=_; rw [slots43]; cases g <;> rfl
theorem good42 (g : Bool) : valid (tail42 g)=true := by
  change (decide (p623.lead≠0 ∧ p623.slot∉slots (tail43 g)) && reads (apart (p623.slot::slots (tail43 g))) p623.num && valid (tail43 g))=true
  rw [slots43,good43]; cases g <;> decide
theorem zero42 (g : Bool) : (tail42 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p623.row=0) && (tail43 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero43]; cases g <;> decide
theorem slots41 (g : Bool) : slots (tail41 g)=[204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p620.slot :: slots (tail42 g)=_; rw [slots42]; cases g <;> rfl
theorem good41 (g : Bool) : valid (tail41 g)=true := by
  change (decide (p620.lead≠0 ∧ p620.slot∉slots (tail42 g)) && reads (apart (p620.slot::slots (tail42 g))) p620.num && valid (tail42 g))=true
  rw [slots42,good42]; cases g <;> decide
theorem zero41 (g : Bool) : (tail41 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p620.row=0) && (tail42 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero42]; cases g <;> decide
theorem slots40 (g : Bool) : slots (tail40 g)=[203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p619.slot :: slots (tail41 g)=_; rw [slots41]; cases g <;> rfl
theorem good40 (g : Bool) : valid (tail40 g)=true := by
  change (decide (p619.lead≠0 ∧ p619.slot∉slots (tail41 g)) && reads (apart (p619.slot::slots (tail41 g))) p619.num && valid (tail41 g))=true
  rw [slots41,good41]; cases g <;> decide
theorem zero40 (g : Bool) : (tail40 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p619.row=0) && (tail41 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero41]; cases g <;> decide
theorem slots39 (g : Bool) : slots (tail39 g)=[154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p364.slot :: slots (tail40 g)=_; rw [slots40]; cases g <;> rfl
theorem good39 (g : Bool) : valid (tail39 g)=true := by
  change (decide (p364.lead≠0 ∧ p364.slot∉slots (tail40 g)) && reads (apart (p364.slot::slots (tail40 g))) p364.num && valid (tail40 g))=true
  rw [slots40,good40]; cases g <;> decide
theorem zero39 (g : Bool) : (tail39 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p364.row=0) && (tail40 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero40]; cases g <;> decide
theorem slots38 (g : Bool) : slots (tail38 g)=[211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p633.slot :: slots (tail39 g)=_; rw [slots39]; cases g <;> rfl
theorem good38 (g : Bool) : valid (tail38 g)=true := by
  change (decide (p633.lead≠0 ∧ p633.slot∉slots (tail39 g)) && reads (apart (p633.slot::slots (tail39 g))) p633.num && valid (tail39 g))=true
  rw [slots39,good39]; cases g <;> decide
theorem zero38 (g : Bool) : (tail38 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p633.row=0) && (tail39 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero39]; cases g <;> decide
theorem slots37 (g : Bool) : slots (tail37 g)=[210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p632.slot :: slots (tail38 g)=_; rw [slots38]; cases g <;> rfl
theorem good37 (g : Bool) : valid (tail37 g)=true := by
  change (decide (p632.lead≠0 ∧ p632.slot∉slots (tail38 g)) && reads (apart (p632.slot::slots (tail38 g))) p632.num && valid (tail38 g))=true
  rw [slots38,good38]; cases g <;> decide
theorem zero37 (g : Bool) : (tail37 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p632.row=0) && (tail38 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero38]; cases g <;> decide
end Triangular.Data
