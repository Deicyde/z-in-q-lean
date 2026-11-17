import PhysicalCoordinates
import DetectorRows
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 12000
set_option maxHeartbeats 600000

theorem pair_rows (k : PPair) (z : Assignment) : rowsHold k.rows z ↔ value z k.f=0 ∧ value z k.g=0 := by
  simp [rowsHold,PPair.rows]

theorem choose_parameters (g : Bool) (x : Assignment) (hp : pivotOK g x) (ds : ∀ k : DBlock,rowsHold k.rows x) :
    ∃ u : DBlock→Rat, ∀k,fits k x (u k) := by
  have choose (k : DBlock) : ∃ u : Rat,fits k x u := by
    have original:=detector_original ((detector_rows g k x hp).mp (ds k))
    exact (CircuitTransport.Detector.projection130 k.den _ _ _ _ _ (by cases k <;> decide)).mp original
  exact ⟨fun k => Classical.choose (choose k),fun k => Classical.choose_spec (choose k)⟩

structure PrivateWitness where
  b : Rat
  c : Rat
  d : Rat

def completes (k : DBlock) (x : Assignment) (w : PrivateWitness) : Prop :=
  let e:=x k.e; let a:=x (k.e+1); let q:=x (k.e+5); let Q:=x (k.e+6)
  e*(1+a*(k.t x)^3)=0 ∧ e*w.b=a^2 ∧ e*a*w.c=w.b^2 ∧ w.c*w.d=(e*a)^5 ∧ w.c*q=w.d^2 ∧ w.c*Q=q^4

def fillPrivate (x : Assignment) (v : DBlock→PrivateWitness) (i : Nat) : Rat :=
  if i=137 then (v .one).b else if i=138 then (v .one).c else if i=139 then (v .one).d else
  if i=149 then (v .two).b else if i=150 then (v .two).c else if i=151 then (v .two).d else
  if i=161 then (v .three).b else if i=162 then (v .three).c else if i=163 then (v .three).d else x i

theorem fillPrivate_off (x : Assignment) (v : DBlock→PrivateWitness) : off privateSlots x (fillPrivate x v) := by
  intro i safe; simp [privateSlots] at safe; simp [fillPrivate,safe]

theorem choose_privates (g : Bool) (y : Fin 130→Rat) (guards : ∀v∈guardValues g y,v=0) :
    ∃ v : DBlock→PrivateWitness, ∀k, completes k (chartPoint g y) (v k) := by
  have chosen (k : DBlock) : ∃ w : PrivateWitness,completes k (chartPoint g y) w := by
    let x:=chartPoint g y; let seed:=seed130 y
    have chartPointMember : CircuitTransport.Detector.Chart130 k.den (x k.e) (k.t x) (x (k.e+1)) (x (k.e+5)) (x (k.e+6)) := by
      obtain ⟨he,ha,hq,hQ⟩:=point_detector g y k
      change CircuitTransport.Detector.Chart130 k.den (chartPoint g y k.e) (k.t (chartPoint g y))
        (chartPoint g y (k.e+1)) (chartPoint g y (k.e+5)) (chartPoint g y (k.e+6))
      rw [he,point_t g y k,ha,hq,hQ]
      exact ⟨seed (k.e+1),(guard_values_iff g y).mp guards k,rfl,rfl,rfl⟩
    obtain ⟨b,c,d,all⟩ := (CircuitTransport.Detector.projection130 k.den _ _ _ _ _ (by cases k <;> decide)).mpr chartPointMember
    exact ⟨⟨b,c,d⟩,all⟩
  exact ⟨fun k => Classical.choose (chosen k),fun k => Classical.choose_spec (chosen k)⟩

theorem private_extension (g : Bool) (x : Assignment) (w : DBlock→PrivateWitness)
    (pivs : pivotOK g x) (all : ∀k, completes k x (w k)) (pade : ∀ k : PPair,rowsHold k.rows x)
    (active : rowsHold (activeRows g) x) : rowsHold (parentRows g) (fillPrivate x w) := by
  let z:=fillPrivate x w
  have offP:=fillPrivate_off x w
  have solved : pivotOK g z := by
    intro p hp
    have same : value z p.row=value x p.row := by
      apply row_congr; intro t ht i hi
      have vis:=reads_slot (physical_visible g p hp).1 ht hi
      exact offP i (by simp [visible,apart] at vis;exact vis.1)
    have clause:=pivot_cell p.pre p.post p.slot p.lead
    exact (clause z).mp (same.trans ((clause x).mpr (pivs p hp)))
  apply (parent_clause _ _ z).mpr
  refine ⟨solved,(split_rows g z).mpr ⟨?_,?_,?_⟩⟩
  · intro r hr
    exact (agree_off offP _ (reads_supported (physical_active g r hr))).trans (active _ hr)
  · intro k; apply (detector_rows g k z solved).mpr
    cases k <;> exact all _
  · intro k
    have small : k.rows.all (fun r => reads (apart privateSlots) r.2)=true := by cases k <;> decide
    intro r hr;exact (agree_off offP _ (reads_supported (List.all_eq_true.mp small r hr))).trans (pade k _ hr)

/-- Both directions use the actual 130-coordinate numbering and the 196 physical signed rows. -/
theorem ordinary_projection (g : Bool) (a : Rat) :
    RowsProject 226 (parentRows g) a ↔ ∃ y : Fin 130→Rat, finiteLift y 1=a ∧ chart g false y := by
  constructor
  · rintro ⟨x,input,old⟩
    obtain ⟨hp,remain⟩ := (parent_clause _ _ _).mp old
    obtain ⟨act,ds,pr⟩ := (split_rows g _).mp remain
    obtain ⟨u,choice⟩ := choose_parameters g (finiteLift x) hp ds
    let y:=candidate (finiteLift x) u
    have outside (i : Nat) (hi : inside i=false) : finiteLift x i=0 := finite_out _ (by simpa [inside] using hi)
    have agrees:=chart_agrees g (finiteLift x) u hp choice (fun k => (pair_rows _ _).mp (pr k)) outside
    have atInput : finiteLift y 1=finiteLift x 1 := (point_input g y).symm.trans (agrees 1 (by decide))
    refine ⟨y,atInput.trans input,?_,?_⟩
    · intro r hr; exact (agree_off agrees _ (reads_supported (physical_active g r hr))).trans (act _ hr)
    · apply (guard_values_iff g y).mpr
      intro k;exact (candidate_values g (finiteLift x) u hp choice k).1
  · rintro ⟨y,hy,active,guards⟩
    obtain ⟨w,selected⟩:=choose_privates g y guards
    let x:=fillPrivate (chartPoint g y) w
    have sol:=private_extension g (chartPoint g y) w (point_pivots g y) selected
      (fun k => (pair_rows _ _).mpr (point_pade g y k)) active
    have outside (i : Nat) (hi : inside i=false) : x i=0 := by
      have insideList : privateSlots.all inside=true := by decide
      have safe : i∉privateSlots := by intro mem; have bad:=List.all_eq_true.mp insideList i mem;rw [hi] at bad;contradiction
      exact (fillPrivate_off _ _ i safe).trans (point_outside g y hi)
    obtain ⟨v,eq⟩:=trunc x outside
    refine ⟨v,?_,?_⟩
    · rw [eq]; exact (fillPrivate_off _ _ 1 (by decide)).trans ((point_input g y).trans hy)
    · rw [eq];exact sol

/-- Exact sum-of-squares polynomial on the same physical parent. -/
theorem ordinary_polynomial (g : Bool) (a : Rat) :
    (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion (parentRows g))=0) ↔
      ∃ y : Fin 130→Rat, finiteLift y 1=a ∧ chart g false y := by
  rw [←ordinary_projection]
  constructor <;> rintro ⟨x,h,v⟩
  · exact ⟨x,h,(RowSquares.zero_iff_rows _ _).mp v⟩
  · exact ⟨x,h,(RowSquares.zero_iff_rows _ _).mpr v⟩

end PhysicalProjection
