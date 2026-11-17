import PhysicalProgram
namespace Physical130
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data CircuitTransport PhysicalProjection

private theorem square_pos (a : Rat) : 0≤a*a := by
  by_cases h : 0≤a
  · exact Rat.mul_nonneg h h
  · have ne : 0≤ -a := by grind
    have pos:=Rat.mul_nonneg ne ne;grind

private theorem sum_pos (b : Book) (x : ProjectionDescent.Assignment) (ws : List Word) : 0≤numerical b x ws := by
  induction ws with | nil => exact Rat.le_refl | cons w ws ih => exact Rat.add_nonneg (square_pos _) ih

private theorem square_value (b : Book) (x : ProjectionDescent.Assignment) (w : Word) (ws : List Word) :
    (squares b w ws).value b x=w.value b x+numerical b x ws := by
  induction ws generalizing w with
  | nil => simp [squares,numerical,Rat.add_zero]
  | cons u ws ih =>
    change (squares b (plus b w (times b u u)) ws).value b x=_
    rw [ih,plus_value,times_value];simp only [numerical];grobner

private theorem sum_zero (b : Book) (x : ProjectionDescent.Assignment) (ws : List Word) :
    numerical b x ws=0 ↔ ∀w∈ws,w.value b x=0 := by
  induction ws with
  | nil => simp [numerical]
  | cons w ws ih =>
    simp only [numerical,List.forall_mem_cons,←ih]
    have h1:=square_pos (w.value b x);have h2:=sum_pos b x ws
    constructor
    · intro eq
      have e : w.value b x*w.value b x=0 := by grind
      exact ⟨(Rat.mul_eq_zero.mp e).elim id id,by grind⟩
    · rintro ⟨r,s⟩;rw [r,s];grobner

private theorem sum_zeros (b : Book) (x : ProjectionDescent.Assignment) (hs ls : List Word) :
    ((combineSums b hs ls).ordinary.value b x=0 ↔ (∀w∈hs,w.value b x=0) ∧ (∀w∈ls,w.value b x=0)) ∧
    ((combineSums b hs ls).marked.value b x=0 ↔ (∀w∈hs,w.value b x=0) ∧ (x 1=0 ∨ ∀w∈ls,w.value b x=0)) := by
  simp only [combineSums,plus_value,times_value,variable_value,square_value,integer_value,Rat.intCast_zero,Rat.zero_add,
    ←sum_zero]
  have h:=sum_pos b x hs;have l:=sum_pos b x ls
  have xl:=Rat.mul_nonneg (square_pos (x 1)) l
  constructor
  · constructor <;> grind
  · constructor
    · intro eq
      have eh : numerical b x hs=0 := by grind
      have zero : x 1*(x 1*numerical b x ls)=0 := by grobner
      rcases Rat.mul_eq_zero.mp zero with a|a
      · exact ⟨eh,Or.inl a⟩
      · exact ⟨eh,Rat.mul_eq_zero.mp a⟩
    · rintro ⟨eh,e|e⟩ <;> grobner

private theorem map_iff {b env cs g} (y : Fin 130→Rat) (rows : Rows) (subset : ∀r∈rows,r∈activeRows g)
    (al : Along b (finiteLift y) env (middle g y))
    (hc : ∀k,CramerCorrect b (finiteLift y) (chartPoint g y) k (cs.atPair k)) :
    (∀w∈rows.map (numerator b env cs),w.value b (finiteLift y)=0) ↔ rowsHold rows (chartPoint g y) := by
  simp only [List.forall_mem_map,rowsHold]
  have eq (r : Nat×Polynomial) (h : r∈rows) :
      (numerator b env cs r).value b (finiteLift y)=0 ↔ value (chartPoint g y) r.2=0 := by
    obtain ⟨ne,e⟩ := every_residual y al cs hc r (subset r h)
    rw [e];exact ⟨fun h=>(Rat.mul_eq_zero.mp h).resolve_left ne,fun h=>by rw [h,Rat.mul_zero]⟩
  constructor
  · intro h r hr;exact (eq r hr).mp (h r hr)
  · intro h r hr;exact (eq r hr).mpr (h r hr)

theorem outputs_chart (b : Book) (g : Bool) (y : Fin 130→Rat) :
    ((outputs130 b g).ordinary.value b (finiteLift y)=0 ↔ chart g false y) ∧
    ((outputs130 b g).marked.value b (finiteLift y)=0 ↔ chart g true y) := by
  let x:=finiteLift y;let ds:=detTable b g;let a:=cells b (ps g) (middleBase b ds)
  let env:=select (middleBase b ds) a;let cs:=makeCram b ds a
  have al : Along b x env (middle g y) := middle_along b g y
  have hc (k : PPair) : CramerCorrect b x (chartPoint g y) k (cs.atPair k) := by
    dsimp only [cs];rw [makeCram_at];exact cramer_correct y k al
  have hs (r) (h : r∈peakRows g) := (List.mem_filter.mp h).1
  have ls (r) (h : r∈lowRows g) := (List.mem_filter.mp (List.mem_mergeSort.mp h)).1
  have high:=map_iff y (peakRows g) hs al hc
  have low:=map_iff y (lowRows g) ls al hc
  have guards : (∀w∈detectors.map (fun k=>(ds.atBlock k).guard),w.value b x=0) ↔ (∀v∈guardValues g y,v=0) := by
    simp only [guardValues,List.forall_mem_map]
    constructor
    · intro h k hk; exact (table_correct b g y k).guard.symm.trans (h k hk)
    · intro h k hk; exact (table_correct b g y k).guard.trans (h k hk)
  have covered : rowsHold (activeRows g) (chartPoint g y) ↔
      rowsHold (peakRows g) (chartPoint g y) ∧ rowsHold (lowRows g) (chartPoint g y) := by
    constructor
    · intro ha; exact ⟨fun r h=>ha r (hs r h),fun r h=>ha r (ls r h)⟩
    · rintro ⟨hi,lo⟩ r hr;cases test:peakIds.contains r.1 with
      | true => exact hi r (List.mem_filter.mpr ⟨hr,test⟩)
      | false => exact lo r (List.mem_mergeSort.mpr (List.mem_filter.mpr ⟨hr,by change (!peakIds.contains r.1)=true;rw [test];rfl⟩))
  have sum:=sum_zeros b (finiteLift y) (highWords b g env cs) (lowWords b g env ds cs)
  have lowAll : (∀ w∈lowWords b g env ds cs,w.value b (finiteLift y)=0) ↔
      rowsHold (lowRows g) (chartPoint g y) ∧ (∀v∈guardValues g y,v=0) := by
    unfold lowWords; rw [List.forall_mem_append,low];exact and_congr_right (fun _=>guards)
  have hHigh : (∀w∈highWords b g env cs,w.value b (finiteLift y)=0) ↔ rowsHold (peakRows g) (chartPoint g y) := high
  have full : (rowsHold (peakRows g) (chartPoint g y) ∧ rowsHold (lowRows g) (chartPoint g y) ∧
    ∀v∈guardValues g y,v=0) ↔ unmarked g y := by
    simp only [unmarked,covered,and_assoc]
  constructor
  · apply sum.1.trans;rw [hHigh,lowAll];exact full
  · apply sum.2.trans;rw [hHigh,lowAll]
    change (_ ∧ (_ ∨ _)) ↔ _ ∧ (_ ∨ unmarked g y)
    constructor
    · rintro ⟨h,z|l⟩
      · exact ⟨h,Or.inl z⟩
      · exact ⟨h,Or.inr (full.mp ⟨h,l⟩)⟩
    · rintro ⟨h,z|u⟩
      · exact ⟨h,Or.inl z⟩
      · exact ⟨h,Or.inr (full.mpr u).2⟩

end Physical130
