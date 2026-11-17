import IndexChecks

namespace IndependentIndices
open CircuitTransport Data
set_option maxRecDepth 20000

theorem bounds :
    (newShape.high.refs++newShape.low.refs).all (fun r=>decide (r.cell<newRoutes.size))=true := by decide

private theorem routed_map (js : Array Nat) (x : Fin 74→Rat) :
    routed js (vector (diagonal x))=routed (js.map parentAt) (vector x) := by
  funext i
  simp only [routed,Array.getElem?_map]
  cases js[i]? with
  | none => rfl
  | some j => exact diagonal_at x j

theorem diag_row (fs : Families) (x : Fin 74→Rat) (r : Ref)
    (mem : r∈newShape.high.refs++newShape.low.refs) :
    rowValue fs newRoutes (vector (diagonal x)) r=rowValue fs oldRoutes (vector x) (srcRef r) := by
  have hr := of_decide_eq_true (List.all_eq_true.mp bounds r mem)
  have ok := Bool.and_eq_true_iff.mp (List.all_eq_true.mp route_checks r.cell (List.mem_range.mpr hr))
  have good := of_decide_eq_true ok.1
  have slots : (oldRoutes[(newRoutes[r.cell]!).family]!).slots=(newRoutes[r.cell]!).slots.map parentAt :=
    Array.toList_inj.mp (by simpa only [Array.toList_map] using good.2)
  dsimp [rowValue,srcRef] at ⊢
  rw [good.1,slots,routed_map]
  rfl

theorem members_congr (fs : Families) (x : Fin 74→Rat) (t s : List Ref) (h : covers t s=true)
    (subset : ∀r∈t,r∈newShape.high.refs++newShape.low.refs) :
    (∀r∈t,rowValue fs newRoutes (vector (diagonal x)) r=0) ↔
      ∀r∈s,rowValue fs oldRoutes (vector x) r=0 := by
  obtain ⟨forward,back⟩:=Bool.and_eq_true_iff.mp h
  constructor
  · intro all r hr
    obtain ⟨q,hq,eq⟩:=List.any_eq_true.mp (List.all_eq_true.mp back r hr)
    have e : srcRef q=r := of_decide_eq_true eq
    rw [←e,←diag_row fs x q (subset q hq)]
    exact all q hq
  · intro all r hr
    rw [diag_row fs x r (subset r hr)]
    obtain ⟨q,hq,eq⟩ := List.any_eq_true.mp (List.all_eq_true.mp forward r hr)
    rw [of_decide_eq_true eq]
    exact all q hq

theorem diagonal_chart (fs : Families) (x : Fin 74→Rat) (m : Bool) :
    conditions newShape fs newRoutes m (vector (diagonal x)) ↔ conditions oldShape fs oldRoutes m (vector x) := by
  have hi:=members_congr fs x _ _ cover_checks.1 (fun _ h=>List.mem_append_left _ h)
  have lo:=members_congr fs x _ _ cover_checks.2 (fun _ h=>List.mem_append_right _ h)
  unfold conditions active
  rw [first_input]
  split
  · exact hi
  · simp only [List.forall_mem_append];exact and_congr hi lo

theorem row_local (fs : Families) (r : Ref) (x y : Assignment)
    (mem : r∈newShape.high.refs++newShape.low.refs)
    (agree : ∀i,inFrame (newRoutes[r.cell]!).frame i=true → x i=y i) :
    rowValue fs newRoutes x r=rowValue fs newRoutes y r := by
  have hr := of_decide_eq_true (List.all_eq_true.mp bounds r mem)
  have ok := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp route_checks r.cell (List.mem_range.mpr hr))).2
  have h : routed (newRoutes[r.cell]!).slots x=routed (newRoutes[r.cell]!).slots y := by
    funext i
    unfold routed
    cases eq : (newRoutes[r.cell]!).slots[i]? with
    | none => rfl
    | some j =>
      apply agree
      exact List.all_eq_true.mp ok j (List.mem_of_getElem? (by simpa using eq))
  dsimp only [rowValue];rw [h]
end IndependentIndices
