import TriClosed
open ZeroInput.Sparse ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem slots73 (g : Bool) : slots (tail73 g)=[] := rfl
theorem good73 (g : Bool) : valid (tail73 g)=true := rfl
theorem zero73 (g : Bool) : (tail73 g).all (fun p => decide (intVal w p.row=0))=true := rfl
theorem slots72 (g : Bool) : slots (tail72 g)=[101] := by
  change p684.slot :: slots (tail73 g)=_; rw [slots73]; cases g <;> rfl
theorem good72 (g : Bool) : valid (tail72 g)=true := by
  change (decide (p684.lead≠0 ∧ p684.slot∉slots (tail73 g)) && reads (apart (p684.slot::slots (tail73 g))) p684.num && valid (tail73 g))=true
  rw [slots73,good73]; cases g <;> decide
theorem zero72 (g : Bool) : (tail72 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p684.row=0) && (tail73 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero73]; cases g <;> decide
theorem slots71 (g : Bool) : slots (tail71 g)=[100,101] := by
  change p683.slot :: slots (tail72 g)=_; rw [slots72]; cases g <;> rfl
theorem good71 (g : Bool) : valid (tail71 g)=true := by
  change (decide (p683.lead≠0 ∧ p683.slot∉slots (tail72 g)) && reads (apart (p683.slot::slots (tail72 g))) p683.num && valid (tail72 g))=true
  rw [slots72,good72]; cases g <;> decide
theorem zero71 (g : Bool) : (tail71 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p683.row=0) && (tail72 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero72]; cases g <;> decide
theorem slots70 (g : Bool) : slots (tail70 g)=[95,100,101] := by
  change p680.slot :: slots (tail71 g)=_; rw [slots71]; cases g <;> rfl
theorem good70 (g : Bool) : valid (tail70 g)=true := by
  change (decide (p680.lead≠0 ∧ p680.slot∉slots (tail71 g)) && reads (apart (p680.slot::slots (tail71 g))) p680.num && valid (tail71 g))=true
  rw [slots71,good71]; cases g <;> decide
theorem zero70 (g : Bool) : (tail70 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p680.row=0) && (tail71 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero71]; cases g <;> decide
theorem slots69 (g : Bool) : slots (tail69 g)=[94,95,100,101] := by
  change p679.slot :: slots (tail70 g)=_; rw [slots70]; cases g <;> rfl
theorem good69 (g : Bool) : valid (tail69 g)=true := by
  change (decide (p679.lead≠0 ∧ p679.slot∉slots (tail70 g)) && reads (apart (p679.slot::slots (tail70 g))) p679.num && valid (tail70 g))=true
  rw [slots70,good70]; cases g <;> decide
theorem zero69 (g : Bool) : (tail69 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p679.row=0) && (tail70 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero70]; cases g <;> decide
theorem slots68 (g : Bool) : slots (tail68 g)=[179,94,95,100,101] := by
  change p564.slot :: slots (tail69 g)=_; rw [slots69]; cases g <;> rfl
theorem good68 (g : Bool) : valid (tail68 g)=true := by
  change (decide (p564.lead≠0 ∧ p564.slot∉slots (tail69 g)) && reads (apart (p564.slot::slots (tail69 g))) p564.num && valid (tail69 g))=true
  rw [slots69,good69]; cases g <;> decide
theorem zero68 (g : Bool) : (tail68 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p564.row=0) && (tail69 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero69]; cases g <;> decide
theorem slots67 (g : Bool) : slots (tail67 g)=[178,179,94,95,100,101] := by
  change (if g then p560b else p560a).slot :: slots (tail68 g)=_; rw [slots68]; cases g <;> rfl
theorem good67 (g : Bool) : valid (tail67 g)=true := by
  change (decide ((if g then p560b else p560a).lead≠0 ∧ (if g then p560b else p560a).slot∉slots (tail68 g)) && reads (apart ((if g then p560b else p560a).slot::slots (tail68 g))) (if g then p560b else p560a).num && valid (tail68 g))=true
  rw [slots68,good68]; cases g <;> decide
theorem zero67 (g : Bool) : (tail67 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w (if g then p560b else p560a).row=0) && (tail68 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero68]; cases g <;> decide
theorem slots66 (g : Bool) : slots (tail66 g)=[169,178,179,94,95,100,101] := by
  change p453.slot :: slots (tail67 g)=_; rw [slots67]; cases g <;> rfl
theorem good66 (g : Bool) : valid (tail66 g)=true := by
  change (decide (p453.lead≠0 ∧ p453.slot∉slots (tail67 g)) && reads (apart (p453.slot::slots (tail67 g))) p453.num && valid (tail67 g))=true
  rw [slots67,good67]; cases g <;> decide
theorem zero66 (g : Bool) : (tail66 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p453.row=0) && (tail67 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero67]; cases g <;> decide
theorem slots65 (g : Bool) : slots (tail65 g)=[226,169,178,179,94,95,100,101] := by
  change p658.slot :: slots (tail66 g)=_; rw [slots66]; cases g <;> rfl
theorem good65 (g : Bool) : valid (tail65 g)=true := by
  change (decide (p658.lead≠0 ∧ p658.slot∉slots (tail66 g)) && reads (apart (p658.slot::slots (tail66 g))) p658.num && valid (tail66 g))=true
  rw [slots66,good66]; cases g <;> decide
theorem zero65 (g : Bool) : (tail65 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p658.row=0) && (tail66 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero66]; cases g <;> decide
theorem slots64 (g : Bool) : slots (tail64 g)=[224,226,169,178,179,94,95,100,101] := by
  change p656.slot :: slots (tail65 g)=_; rw [slots65]; cases g <;> rfl
theorem good64 (g : Bool) : valid (tail64 g)=true := by
  change (decide (p656.lead≠0 ∧ p656.slot∉slots (tail65 g)) && reads (apart (p656.slot::slots (tail65 g))) p656.num && valid (tail65 g))=true
  rw [slots65,good65]; cases g <;> decide
theorem zero64 (g : Bool) : (tail64 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p656.row=0) && (tail65 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero65]; cases g <;> decide
end Triangular.Data
