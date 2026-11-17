import TriChain4
open ZeroInput.Sparse ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem slots27 (g : Bool) : slots (tail27 g)=[185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p586.slot :: slots (tail28 g)=_; rw [slots28]; cases g <;> rfl
theorem good27 (g : Bool) : valid (tail27 g)=true := by
  change (decide (p586.lead≠0 ∧ p586.slot∉slots (tail28 g)) && reads (apart (p586.slot::slots (tail28 g))) p586.num && valid (tail28 g))=true
  rw [slots28,good28]; cases g <;> decide
theorem zero27 (g : Bool) : (tail27 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p586.row=0) && (tail28 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero28]; cases g <;> decide
theorem slots26 (g : Bool) : slots (tail26 g)=[184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p585.slot :: slots (tail27 g)=_; rw [slots27]; cases g <;> rfl
theorem good26 (g : Bool) : valid (tail26 g)=true := by
  change (decide (p585.lead≠0 ∧ p585.slot∉slots (tail27 g)) && reads (apart (p585.slot::slots (tail27 g))) p585.num && valid (tail27 g))=true
  rw [slots27,good27]; cases g <;> decide
theorem zero26 (g : Bool) : (tail26 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p585.row=0) && (tail27 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero27]; cases g <;> decide
theorem slots25 (g : Bool) : slots (tail25 g)=[196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p604.slot :: slots (tail26 g)=_; rw [slots26]; cases g <;> rfl
theorem good25 (g : Bool) : valid (tail25 g)=true := by
  change (decide (p604.lead≠0 ∧ p604.slot∉slots (tail26 g)) && reads (apart (p604.slot::slots (tail26 g))) p604.num && valid (tail26 g))=true
  rw [slots26,good26]; cases g <;> decide
theorem zero25 (g : Bool) : (tail25 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p604.row=0) && (tail26 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero26]; cases g <;> decide
theorem slots24 (g : Bool) : slots (tail24 g)=[195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p603.slot :: slots (tail25 g)=_; rw [slots25]; cases g <;> rfl
theorem good24 (g : Bool) : valid (tail24 g)=true := by
  change (decide (p603.lead≠0 ∧ p603.slot∉slots (tail25 g)) && reads (apart (p603.slot::slots (tail25 g))) p603.num && valid (tail25 g))=true
  rw [slots25,good25]; cases g <;> decide
theorem zero24 (g : Bool) : (tail24 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p603.row=0) && (tail25 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero25]; cases g <;> decide
theorem slots23 (g : Bool) : slots (tail23 g)=[89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p151.slot :: slots (tail24 g)=_; rw [slots24]; cases g <;> rfl
theorem good23 (g : Bool) : valid (tail23 g)=true := by
  change (decide (p151.lead≠0 ∧ p151.slot∉slots (tail24 g)) && reads (apart (p151.slot::slots (tail24 g))) p151.num && valid (tail24 g))=true
  rw [slots24,good24]; cases g <;> decide
theorem zero23 (g : Bool) : (tail23 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p151.row=0) && (tail24 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero24]; cases g <;> decide
theorem slots22 (g : Bool) : slots (tail22 g)=[88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p150.slot :: slots (tail23 g)=_; rw [slots23]; cases g <;> rfl
theorem good22 (g : Bool) : valid (tail22 g)=true := by
  change (decide (p150.lead≠0 ∧ p150.slot∉slots (tail23 g)) && reads (apart (p150.slot::slots (tail23 g))) p150.num && valid (tail23 g))=true
  rw [slots23,good23]; cases g <;> decide
theorem zero22 (g : Bool) : (tail22 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p150.row=0) && (tail23 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero23]; cases g <;> decide
theorem slots21 (g : Bool) : slots (tail21 g)=[194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p602.slot :: slots (tail22 g)=_; rw [slots22]; cases g <;> rfl
theorem good21 (g : Bool) : valid (tail21 g)=true := by
  change (decide (p602.lead≠0 ∧ p602.slot∉slots (tail22 g)) && reads (apart (p602.slot::slots (tail22 g))) p602.num && valid (tail22 g))=true
  rw [slots22,good22]; cases g <;> decide
theorem zero21 (g : Bool) : (tail21 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p602.row=0) && (tail22 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero22]; cases g <;> decide
theorem slots20 (g : Bool) : slots (tail20 g)=[183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p580.slot :: slots (tail21 g)=_; rw [slots21]; cases g <;> rfl
theorem good20 (g : Bool) : valid (tail20 g)=true := by
  change (decide (p580.lead≠0 ∧ p580.slot∉slots (tail21 g)) && reads (apart (p580.slot::slots (tail21 g))) p580.num && valid (tail21 g))=true
  rw [slots21,good21]; cases g <;> decide
theorem zero20 (g : Bool) : (tail20 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p580.row=0) && (tail21 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero21]; cases g <;> decide
theorem slots19 (g : Bool) : slots (tail19 g)=[182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p581.slot :: slots (tail20 g)=_; rw [slots20]; cases g <;> rfl
theorem good19 (g : Bool) : valid (tail19 g)=true := by
  change (decide (p581.lead≠0 ∧ p581.slot∉slots (tail20 g)) && reads (apart (p581.slot::slots (tail20 g))) p581.num && valid (tail20 g))=true
  rw [slots20,good20]; cases g <;> decide
theorem zero19 (g : Bool) : (tail19 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p581.row=0) && (tail20 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero20]; cases g <;> decide
end Triangular.Data
