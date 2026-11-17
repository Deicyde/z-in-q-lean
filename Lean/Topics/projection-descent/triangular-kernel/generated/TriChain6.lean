import TriChain5
open ZeroInput.Sparse ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem slots18 (g : Bool) : slots (tail18 g)=[193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p601.slot :: slots (tail19 g)=_; rw [slots19]; cases g <;> rfl
theorem good18 (g : Bool) : valid (tail18 g)=true := by
  change (decide (p601.lead≠0 ∧ p601.slot∉slots (tail19 g)) && reads (apart (p601.slot::slots (tail19 g))) p601.num && valid (tail19 g))=true
  rw [slots19,good19]; cases g <;> decide
theorem zero18 (g : Bool) : (tail18 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p601.row=0) && (tail19 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero19]; cases g <;> decide
theorem slots17 (g : Bool) : slots (tail17 g)=[79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p133.slot :: slots (tail18 g)=_; rw [slots18]; cases g <;> rfl
theorem good17 (g : Bool) : valid (tail17 g)=true := by
  change (decide (p133.lead≠0 ∧ p133.slot∉slots (tail18 g)) && reads (apart (p133.slot::slots (tail18 g))) p133.num && valid (tail18 g))=true
  rw [slots18,good18]; cases g <;> decide
theorem zero17 (g : Bool) : (tail17 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p133.row=0) && (tail18 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero18]; cases g <;> decide
theorem slots16 (g : Bool) : slots (tail16 g)=[78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p132.slot :: slots (tail17 g)=_; rw [slots17]; cases g <;> rfl
theorem good16 (g : Bool) : valid (tail16 g)=true := by
  change (decide (p132.lead≠0 ∧ p132.slot∉slots (tail17 g)) && reads (apart (p132.slot::slots (tail17 g))) p132.num && valid (tail17 g))=true
  rw [slots17,good17]; cases g <;> decide
theorem zero16 (g : Bool) : (tail16 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p132.row=0) && (tail17 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero17]; cases g <;> decide
theorem slots15 (g : Bool) : slots (tail15 g)=[192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p598.slot :: slots (tail16 g)=_; rw [slots16]; cases g <;> rfl
theorem good15 (g : Bool) : valid (tail15 g)=true := by
  change (decide (p598.lead≠0 ∧ p598.slot∉slots (tail16 g)) && reads (apart (p598.slot::slots (tail16 g))) p598.num && valid (tail16 g))=true
  rw [slots16,good16]; cases g <;> decide
theorem zero15 (g : Bool) : (tail15 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p598.row=0) && (tail16 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero16]; cases g <;> decide
theorem slots14 (g : Bool) : slots (tail14 g)=[181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p568.slot :: slots (tail15 g)=_; rw [slots15]; cases g <;> rfl
theorem good14 (g : Bool) : valid (tail14 g)=true := by
  change (decide (p568.lead≠0 ∧ p568.slot∉slots (tail15 g)) && reads (apart (p568.slot::slots (tail15 g))) p568.num && valid (tail15 g))=true
  rw [slots15,good15]; cases g <;> decide
theorem zero14 (g : Bool) : (tail14 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p568.row=0) && (tail15 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero15]; cases g <;> decide
theorem slots13 (g : Bool) : slots (tail13 g)=[180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p569.slot :: slots (tail14 g)=_; rw [slots14]; cases g <;> rfl
theorem good13 (g : Bool) : valid (tail13 g)=true := by
  change (decide (p569.lead≠0 ∧ p569.slot∉slots (tail14 g)) && reads (apart (p569.slot::slots (tail14 g))) p569.num && valid (tail14 g))=true
  rw [slots14,good14]; cases g <;> decide
theorem zero13 (g : Bool) : (tail13 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p569.row=0) && (tail14 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero14]; cases g <;> decide
theorem slots12 (g : Bool) : slots (tail12 g)=[191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p597.slot :: slots (tail13 g)=_; rw [slots13]; cases g <;> rfl
theorem good12 (g : Bool) : valid (tail12 g)=true := by
  change (decide (p597.lead≠0 ∧ p597.slot∉slots (tail13 g)) && reads (apart (p597.slot::slots (tail13 g))) p597.num && valid (tail13 g))=true
  rw [slots13,good13]; cases g <;> decide
theorem zero12 (g : Bool) : (tail12 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p597.row=0) && (tail13 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero13]; cases g <;> decide
theorem slots11 (g : Bool) : slots (tail11 g)=[142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p314.slot :: slots (tail12 g)=_; rw [slots12]; cases g <;> rfl
theorem good11 (g : Bool) : valid (tail11 g)=true := by
  change (decide (p314.lead≠0 ∧ p314.slot∉slots (tail12 g)) && reads (apart (p314.slot::slots (tail12 g))) p314.num && valid (tail12 g))=true
  rw [slots12,good12]; cases g <;> decide
theorem zero11 (g : Bool) : (tail11 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p314.row=0) && (tail12 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero12]; cases g <;> decide
theorem slots10 (g : Bool) : slots (tail10 g)=[199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p611.slot :: slots (tail11 g)=_; rw [slots11]; cases g <;> rfl
theorem good10 (g : Bool) : valid (tail10 g)=true := by
  change (decide (p611.lead≠0 ∧ p611.slot∉slots (tail11 g)) && reads (apart (p611.slot::slots (tail11 g))) p611.num && valid (tail11 g))=true
  rw [slots11,good11]; cases g <;> decide
theorem zero10 (g : Bool) : (tail10 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p611.row=0) && (tail11 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero11]; cases g <;> decide
end Triangular.Data
