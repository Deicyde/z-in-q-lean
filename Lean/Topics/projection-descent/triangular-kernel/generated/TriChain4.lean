import TriChain3
open ZeroInput.Sparse ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem slots36 (g : Bool) : slots (tail36 g)=[209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p631.slot :: slots (tail37 g)=_; rw [slots37]; cases g <;> rfl
theorem good36 (g : Bool) : valid (tail36 g)=true := by
  change (decide (p631.lead≠0 ∧ p631.slot∉slots (tail37 g)) && reads (apart (p631.slot::slots (tail37 g))) p631.num && valid (tail37 g))=true
  rw [slots37,good37]; cases g <;> decide
theorem zero36 (g : Bool) : (tail36 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p631.row=0) && (tail37 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero37]; cases g <;> decide
theorem slots35 (g : Bool) : slots (tail35 g)=[146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p350.slot :: slots (tail36 g)=_; rw [slots36]; cases g <;> rfl
theorem good35 (g : Bool) : valid (tail35 g)=true := by
  change (decide (p350.lead≠0 ∧ p350.slot∉slots (tail36 g)) && reads (apart (p350.slot::slots (tail36 g))) p350.num && valid (tail36 g))=true
  rw [slots36,good36]; cases g <;> decide
theorem zero35 (g : Bool) : (tail35 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p350.row=0) && (tail36 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero36]; cases g <;> decide
theorem slots34 (g : Bool) : slots (tail34 g)=[145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p345.slot :: slots (tail35 g)=_; rw [slots35]; cases g <;> rfl
theorem good34 (g : Bool) : valid (tail34 g)=true := by
  change (decide (p345.lead≠0 ∧ p345.slot∉slots (tail35 g)) && reads (apart (p345.slot::slots (tail35 g))) p345.num && valid (tail35 g))=true
  rw [slots35,good35]; cases g <;> decide
theorem zero34 (g : Bool) : (tail34 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p345.row=0) && (tail35 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero35]; cases g <;> decide
theorem slots33 (g : Bool) : slots (tail33 g)=[132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p295.slot :: slots (tail34 g)=_; rw [slots34]; cases g <;> rfl
theorem good33 (g : Bool) : valid (tail33 g)=true := by
  change (decide (p295.lead≠0 ∧ p295.slot∉slots (tail34 g)) && reads (apart (p295.slot::slots (tail34 g))) p295.num && valid (tail34 g))=true
  rw [slots34,good34]; cases g <;> decide
theorem zero33 (g : Bool) : (tail33 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p295.row=0) && (tail34 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero34]; cases g <;> decide
theorem slots32 (g : Bool) : slots (tail32 g)=[131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p292.slot :: slots (tail33 g)=_; rw [slots33]; cases g <;> rfl
theorem good32 (g : Bool) : valid (tail32 g)=true := by
  change (decide (p292.lead≠0 ∧ p292.slot∉slots (tail33 g)) && reads (apart (p292.slot::slots (tail33 g))) p292.num && valid (tail33 g))=true
  rw [slots33,good33]; cases g <;> decide
theorem zero32 (g : Bool) : (tail32 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p292.row=0) && (tail33 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero33]; cases g <;> decide
theorem slots31 (g : Bool) : slots (tail31 g)=[130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p291.slot :: slots (tail32 g)=_; rw [slots32]; cases g <;> rfl
theorem good31 (g : Bool) : valid (tail31 g)=true := by
  change (decide (p291.lead≠0 ∧ p291.slot∉slots (tail32 g)) && reads (apart (p291.slot::slots (tail32 g))) p291.num && valid (tail32 g))=true
  rw [slots32,good32]; cases g <;> decide
theorem zero31 (g : Bool) : (tail31 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p291.row=0) && (tail32 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero32]; cases g <;> decide
theorem slots30 (g : Bool) : slots (tail30 g)=[202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p614.slot :: slots (tail31 g)=_; rw [slots31]; cases g <;> rfl
theorem good30 (g : Bool) : valid (tail30 g)=true := by
  change (decide (p614.lead≠0 ∧ p614.slot∉slots (tail31 g)) && reads (apart (p614.slot::slots (tail31 g))) p614.num && valid (tail31 g))=true
  rw [slots31,good31]; cases g <;> decide
theorem zero30 (g : Bool) : (tail30 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p614.row=0) && (tail31 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero31]; cases g <;> decide
theorem slots29 (g : Bool) : slots (tail29 g)=[200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p612.slot :: slots (tail30 g)=_; rw [slots30]; cases g <;> rfl
theorem good29 (g : Bool) : valid (tail29 g)=true := by
  change (decide (p612.lead≠0 ∧ p612.slot∉slots (tail30 g)) && reads (apart (p612.slot::slots (tail30 g))) p612.num && valid (tail30 g))=true
  rw [slots30,good30]; cases g <;> decide
theorem zero29 (g : Bool) : (tail29 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p612.row=0) && (tail30 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero30]; cases g <;> decide
theorem slots28 (g : Bool) : slots (tail28 g)=[201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p613.slot :: slots (tail29 g)=_; rw [slots29]; cases g <;> rfl
theorem good28 (g : Bool) : valid (tail28 g)=true := by
  change (decide (p613.lead≠0 ∧ p613.slot∉slots (tail29 g)) && reads (apart (p613.slot::slots (tail29 g))) p613.num && valid (tail29 g))=true
  rw [slots29,good29]; cases g <;> decide
theorem zero28 (g : Bool) : (tail28 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p613.row=0) && (tail29 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero29]; cases g <;> decide
end Triangular.Data
