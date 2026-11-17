import TriChain6
open ZeroInput.Sparse ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem slots9 (g : Bool) : slots (tail9 g)=[187,199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p588.slot :: slots (tail10 g)=_; rw [slots10]; cases g <;> rfl
theorem good9 (g : Bool) : valid (tail9 g)=true := by
  change (decide (p588.lead≠0 ∧ p588.slot∉slots (tail10 g)) && reads (apart (p588.slot::slots (tail10 g))) p588.num && valid (tail10 g))=true
  rw [slots10,good10]; cases g <;> decide
theorem zero9 (g : Bool) : (tail9 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p588.row=0) && (tail10 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero10]; cases g <;> decide
theorem slots8 (g : Bool) : slots (tail8 g)=[186,187,199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p587.slot :: slots (tail9 g)=_; rw [slots9]; cases g <;> rfl
theorem good8 (g : Bool) : valid (tail8 g)=true := by
  change (decide (p587.lead≠0 ∧ p587.slot∉slots (tail9 g)) && reads (apart (p587.slot::slots (tail9 g))) p587.num && valid (tail9 g))=true
  rw [slots9,good9]; cases g <;> decide
theorem zero8 (g : Bool) : (tail8 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p587.row=0) && (tail9 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero9]; cases g <;> decide
theorem slots7 (g : Bool) : slots (tail7 g)=[198,186,187,199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p610.slot :: slots (tail8 g)=_; rw [slots8]; cases g <;> rfl
theorem good7 (g : Bool) : valid (tail7 g)=true := by
  change (decide (p610.lead≠0 ∧ p610.slot∉slots (tail8 g)) && reads (apart (p610.slot::slots (tail8 g))) p610.num && valid (tail8 g))=true
  rw [slots8,good8]; cases g <;> decide
theorem zero7 (g : Bool) : (tail7 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p610.row=0) && (tail8 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero8]; cases g <;> decide
theorem slots6 (g : Bool) : slots (tail6 g)=[197,198,186,187,199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p609.slot :: slots (tail7 g)=_; rw [slots7]; cases g <;> rfl
theorem good6 (g : Bool) : valid (tail6 g)=true := by
  change (decide (p609.lead≠0 ∧ p609.slot∉slots (tail7 g)) && reads (apart (p609.slot::slots (tail7 g))) p609.num && valid (tail7 g))=true
  rw [slots7,good7]; cases g <;> decide
theorem zero6 (g : Bool) : (tail6 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p609.row=0) && (tail7 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero7]; cases g <;> decide
theorem slots5 (g : Bool) : slots (tail5 g)=[190,197,198,186,187,199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p592.slot :: slots (tail6 g)=_; rw [slots6]; cases g <;> rfl
theorem good5 (g : Bool) : valid (tail5 g)=true := by
  change (decide (p592.lead≠0 ∧ p592.slot∉slots (tail6 g)) && reads (apart (p592.slot::slots (tail6 g))) p592.num && valid (tail6 g))=true
  rw [slots6,good6]; cases g <;> decide
theorem zero5 (g : Bool) : (tail5 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p592.row=0) && (tail6 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero6]; cases g <;> decide
theorem slots4 (g : Bool) : slots (tail4 g)=[188,190,197,198,186,187,199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p590.slot :: slots (tail5 g)=_; rw [slots5]; cases g <;> rfl
theorem good4 (g : Bool) : valid (tail4 g)=true := by
  change (decide (p590.lead≠0 ∧ p590.slot∉slots (tail5 g)) && reads (apart (p590.slot::slots (tail5 g))) p590.num && valid (tail5 g))=true
  rw [slots5,good5]; cases g <;> decide
theorem zero4 (g : Bool) : (tail4 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p590.row=0) && (tail5 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero5]; cases g <;> decide
theorem slots3 (g : Bool) : slots (tail3 g)=[175,188,190,197,198,186,187,199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p511.slot :: slots (tail4 g)=_; rw [slots4]; cases g <;> rfl
theorem good3 (g : Bool) : valid (tail3 g)=true := by
  change (decide (p511.lead≠0 ∧ p511.slot∉slots (tail4 g)) && reads (apart (p511.slot::slots (tail4 g))) p511.num && valid (tail4 g))=true
  rw [slots4,good4]; cases g <;> decide
theorem zero3 (g : Bool) : (tail3 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p511.row=0) && (tail4 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero4]; cases g <;> decide
theorem slots2 (g : Bool) : slots (tail2 g)=[189,175,188,190,197,198,186,187,199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p591.slot :: slots (tail3 g)=_; rw [slots3]; cases g <;> rfl
theorem good2 (g : Bool) : valid (tail2 g)=true := by
  change (decide (p591.lead≠0 ∧ p591.slot∉slots (tail3 g)) && reads (apart (p591.slot::slots (tail3 g))) p591.num && valid (tail3 g))=true
  rw [slots3,good3]; cases g <;> decide
theorem zero2 (g : Bool) : (tail2 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p591.row=0) && (tail3 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero3]; cases g <;> decide
theorem slots1 (g : Bool) : slots (tail1 g)=[121,189,175,188,190,197,198,186,187,199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p206.slot :: slots (tail2 g)=_; rw [slots2]; cases g <;> rfl
theorem good1 (g : Bool) : valid (tail1 g)=true := by
  change (decide (p206.lead≠0 ∧ p206.slot∉slots (tail2 g)) && reads (apart (p206.slot::slots (tail2 g))) p206.num && valid (tail2 g))=true
  rw [slots2,good2]; cases g <;> decide
theorem zero1 (g : Bool) : (tail1 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p206.row=0) && (tail2 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero2]; cases g <;> decide
end Triangular.Data
