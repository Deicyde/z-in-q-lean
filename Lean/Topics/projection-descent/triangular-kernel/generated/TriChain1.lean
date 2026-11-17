import TriChain0
open ZeroInput.Sparse ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem slots63 (g : Bool) : slots (tail63 g)=[225,224,226,169,178,179,94,95,100,101] := by
  change p657.slot :: slots (tail64 g)=_; rw [slots64]; cases g <;> rfl
theorem good63 (g : Bool) : valid (tail63 g)=true := by
  change (decide (p657.lead≠0 ∧ p657.slot∉slots (tail64 g)) && reads (apart (p657.slot::slots (tail64 g))) p657.num && valid (tail64 g))=true
  rw [slots64,good64]; cases g <;> decide
theorem zero63 (g : Bool) : (tail63 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p657.row=0) && (tail64 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero64]; cases g <;> decide
theorem slots62 (g : Bool) : slots (tail62 g)=[220,225,224,226,169,178,179,94,95,100,101] := by
  change p648.slot :: slots (tail63 g)=_; rw [slots63]; cases g <;> rfl
theorem good62 (g : Bool) : valid (tail62 g)=true := by
  change (decide (p648.lead≠0 ∧ p648.slot∉slots (tail63 g)) && reads (apart (p648.slot::slots (tail63 g))) p648.num && valid (tail63 g))=true
  rw [slots63,good63]; cases g <;> decide
theorem zero62 (g : Bool) : (tail62 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p648.row=0) && (tail63 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero63]; cases g <;> decide
theorem slots61 (g : Bool) : slots (tail61 g)=[219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p647.slot :: slots (tail62 g)=_; rw [slots62]; cases g <;> rfl
theorem good61 (g : Bool) : valid (tail61 g)=true := by
  change (decide (p647.lead≠0 ∧ p647.slot∉slots (tail62 g)) && reads (apart (p647.slot::slots (tail62 g))) p647.num && valid (tail62 g))=true
  rw [slots62,good62]; cases g <;> decide
theorem zero61 (g : Bool) : (tail61 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p647.row=0) && (tail62 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero62]; cases g <;> decide
theorem slots60 (g : Bool) : slots (tail60 g)=[218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p646.slot :: slots (tail61 g)=_; rw [slots61]; cases g <;> rfl
theorem good60 (g : Bool) : valid (tail60 g)=true := by
  change (decide (p646.lead≠0 ∧ p646.slot∉slots (tail61 g)) && reads (apart (p646.slot::slots (tail61 g))) p646.num && valid (tail61 g))=true
  rw [slots61,good61]; cases g <;> decide
theorem zero60 (g : Bool) : (tail60 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p646.row=0) && (tail61 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero61]; cases g <;> decide
theorem slots59 (g : Bool) : slots (tail59 g)=[217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p645.slot :: slots (tail60 g)=_; rw [slots60]; cases g <;> rfl
theorem good59 (g : Bool) : valid (tail59 g)=true := by
  change (decide (p645.lead≠0 ∧ p645.slot∉slots (tail60 g)) && reads (apart (p645.slot::slots (tail60 g))) p645.num && valid (tail60 g))=true
  rw [slots60,good60]; cases g <;> decide
theorem zero59 (g : Bool) : (tail59 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p645.row=0) && (tail60 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero60]; cases g <;> decide
theorem slots58 (g : Bool) : slots (tail58 g)=[216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p642.slot :: slots (tail59 g)=_; rw [slots59]; cases g <;> rfl
theorem good58 (g : Bool) : valid (tail58 g)=true := by
  change (decide (p642.lead≠0 ∧ p642.slot∉slots (tail59 g)) && reads (apart (p642.slot::slots (tail59 g))) p642.num && valid (tail59 g))=true
  rw [slots59,good59]; cases g <;> decide
theorem zero58 (g : Bool) : (tail58 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p642.row=0) && (tail59 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero59]; cases g <;> decide
theorem slots57 (g : Bool) : slots (tail57 g)=[215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p641.slot :: slots (tail58 g)=_; rw [slots58]; cases g <;> rfl
theorem good57 (g : Bool) : valid (tail57 g)=true := by
  change (decide (p641.lead≠0 ∧ p641.slot∉slots (tail58 g)) && reads (apart (p641.slot::slots (tail58 g))) p641.num && valid (tail58 g))=true
  rw [slots58,good58]; cases g <;> decide
theorem zero57 (g : Bool) : (tail57 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p641.row=0) && (tail58 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero58]; cases g <;> decide
theorem slots56 (g : Bool) : slots (tail56 g)=[166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p414.slot :: slots (tail57 g)=_; rw [slots57]; cases g <;> rfl
theorem good56 (g : Bool) : valid (tail56 g)=true := by
  change (decide (p414.lead≠0 ∧ p414.slot∉slots (tail57 g)) && reads (apart (p414.slot::slots (tail57 g))) p414.num && valid (tail57 g))=true
  rw [slots57,good57]; cases g <;> decide
theorem zero56 (g : Bool) : (tail56 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p414.row=0) && (tail57 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero57]; cases g <;> decide
theorem slots55 (g : Bool) : slots (tail55 g)=[223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p655.slot :: slots (tail56 g)=_; rw [slots56]; cases g <;> rfl
theorem good55 (g : Bool) : valid (tail55 g)=true := by
  change (decide (p655.lead≠0 ∧ p655.slot∉slots (tail56 g)) && reads (apart (p655.slot::slots (tail56 g))) p655.num && valid (tail56 g))=true
  rw [slots56,good56]; cases g <;> decide
theorem zero55 (g : Bool) : (tail55 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p655.row=0) && (tail56 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero56]; cases g <;> decide
end Triangular.Data
