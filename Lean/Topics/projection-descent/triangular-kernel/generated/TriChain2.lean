import TriChain1
open ZeroInput.Sparse ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
theorem slots54 (g : Bool) : slots (tail54 g)=[222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p654.slot :: slots (tail55 g)=_; rw [slots55]; cases g <;> rfl
theorem good54 (g : Bool) : valid (tail54 g)=true := by
  change (decide (p654.lead≠0 ∧ p654.slot∉slots (tail55 g)) && reads (apart (p654.slot::slots (tail55 g))) p654.num && valid (tail55 g))=true
  rw [slots55,good55]; cases g <;> decide
theorem zero54 (g : Bool) : (tail54 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p654.row=0) && (tail55 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero55]; cases g <;> decide
theorem slots53 (g : Bool) : slots (tail53 g)=[221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p653.slot :: slots (tail54 g)=_; rw [slots54]; cases g <;> rfl
theorem good53 (g : Bool) : valid (tail53 g)=true := by
  change (decide (p653.lead≠0 ∧ p653.slot∉slots (tail54 g)) && reads (apart (p653.slot::slots (tail54 g))) p653.num && valid (tail54 g))=true
  rw [slots54,good54]; cases g <;> decide
theorem zero53 (g : Bool) : (tail53 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p653.row=0) && (tail54 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero54]; cases g <;> decide
theorem slots52 (g : Bool) : slots (tail52 g)=[158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p399.slot :: slots (tail53 g)=_; rw [slots53]; cases g <;> rfl
theorem good52 (g : Bool) : valid (tail52 g)=true := by
  change (decide (p399.lead≠0 ∧ p399.slot∉slots (tail53 g)) && reads (apart (p399.slot::slots (tail53 g))) p399.num && valid (tail53 g))=true
  rw [slots53,good53]; cases g <;> decide
theorem zero52 (g : Bool) : (tail52 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p399.row=0) && (tail53 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero53]; cases g <;> decide
theorem slots51 (g : Bool) : slots (tail51 g)=[157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p395.slot :: slots (tail52 g)=_; rw [slots52]; cases g <;> rfl
theorem good51 (g : Bool) : valid (tail51 g)=true := by
  change (decide (p395.lead≠0 ∧ p395.slot∉slots (tail52 g)) && reads (apart (p395.slot::slots (tail52 g))) p395.num && valid (tail52 g))=true
  rw [slots52,good52]; cases g <;> decide
theorem zero51 (g : Bool) : (tail51 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p395.row=0) && (tail52 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero52]; cases g <;> decide
theorem slots50 (g : Bool) : slots (tail50 g)=[134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p297.slot :: slots (tail51 g)=_; rw [slots51]; cases g <;> rfl
theorem good50 (g : Bool) : valid (tail50 g)=true := by
  change (decide (p297.lead≠0 ∧ p297.slot∉slots (tail51 g)) && reads (apart (p297.slot::slots (tail51 g))) p297.num && valid (tail51 g))=true
  rw [slots51,good51]; cases g <;> decide
theorem zero50 (g : Bool) : (tail50 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p297.row=0) && (tail51 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero51]; cases g <;> decide
theorem slots49 (g : Bool) : slots (tail49 g)=[133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p296.slot :: slots (tail50 g)=_; rw [slots50]; cases g <;> rfl
theorem good49 (g : Bool) : valid (tail49 g)=true := by
  change (decide (p296.lead≠0 ∧ p296.slot∉slots (tail50 g)) && reads (apart (p296.slot::slots (tail50 g))) p296.num && valid (tail50 g))=true
  rw [slots50,good50]; cases g <;> decide
theorem zero49 (g : Bool) : (tail49 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p296.row=0) && (tail50 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero50]; cases g <;> decide
theorem slots48 (g : Bool) : slots (tail48 g)=[214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p636.slot :: slots (tail49 g)=_; rw [slots49]; cases g <;> rfl
theorem good48 (g : Bool) : valid (tail48 g)=true := by
  change (decide (p636.lead≠0 ∧ p636.slot∉slots (tail49 g)) && reads (apart (p636.slot::slots (tail49 g))) p636.num && valid (tail49 g))=true
  rw [slots49,good49]; cases g <;> decide
theorem zero48 (g : Bool) : (tail48 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p636.row=0) && (tail49 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero49]; cases g <;> decide
theorem slots47 (g : Bool) : slots (tail47 g)=[212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p634.slot :: slots (tail48 g)=_; rw [slots48]; cases g <;> rfl
theorem good47 (g : Bool) : valid (tail47 g)=true := by
  change (decide (p634.lead≠0 ∧ p634.slot∉slots (tail48 g)) && reads (apart (p634.slot::slots (tail48 g))) p634.num && valid (tail48 g))=true
  rw [slots48,good48]; cases g <;> decide
theorem zero47 (g : Bool) : (tail47 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p634.row=0) && (tail48 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero48]; cases g <;> decide
theorem slots46 (g : Bool) : slots (tail46 g)=[213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101] := by
  change p635.slot :: slots (tail47 g)=_; rw [slots47]; cases g <;> rfl
theorem good46 (g : Bool) : valid (tail46 g)=true := by
  change (decide (p635.lead≠0 ∧ p635.slot∉slots (tail47 g)) && reads (apart (p635.slot::slots (tail47 g))) p635.num && valid (tail47 g))=true
  rw [slots47,good47]; cases g <;> decide
theorem zero46 (g : Bool) : (tail46 g).all (fun p => decide (intVal w p.row=0))=true := by
  change (decide (intVal w p635.row=0) && (tail47 g).all (fun p => decide (intVal w p.row=0)))=true; rw [zero47]; cases g <;> decide
end Triangular.Data
