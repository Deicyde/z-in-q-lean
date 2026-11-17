import CramerCells
namespace Physical130
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data CircuitTransport PhysicalProjection

structure DetTable where
  first : Detector
  second : Detector
  third : Detector

def DetTable.atBlock (d : DetTable) : DBlock→Detector | .one=>d.first | .two=>d.second | .three=>d.third

@[noinline] def makeDet (b : Book) (a : Array (Option Cell)) : DetTable :=
  let env := select (base b) a
  ⟨detWords b .one env,detWords b .two env,detWords b .three env⟩

def detTable (b : Book) (gate : Bool) := makeDet b (cells b (ps gate) (base b))

theorem table_correct (b : Book) (g : Bool) (y : Fin 130→Rat) (k : DBlock) :
    DetCorrect b (finiteLift y) k ((detTable b g).atBlock k) (preliminary g y) (seed130 y) := by
  have h:=detector_values b g y k; cases k <;> exact h

def middleBase (b : Book) (d : DetTable) := material b d.atBlock

theorem middle_along (b : Book) (gate : Bool) (y : Fin 130→Rat) :
    Along b (finiteLift y) (memo b (ps gate) (middleBase b (detTable b gate))) (middle gate y) := by
  rw [memo_eq]
  exact restore_value (material_along b y _ _ (table_correct b gate y)) _ (good0 gate)

structure CramTable where
  first : Triple
  second : Triple
  third : Triple
  fourth : Triple

def CramTable.atPair (c : CramTable) : PPair→Triple
  | .one=>c.first | .two=>c.second | .three=>c.third | .four=>c.fourth

@[noinline] def makeCram (b : Book) (ds : DetTable) (a : Array (Option Cell)) : CramTable :=
  let env := select (middleBase b ds) a
  ⟨cramer b env .one,cramer b env .two,cramer b env .three,cramer b env .four⟩

theorem makeCram_at (b : Book) (ds : DetTable) (a : Array (Option Cell)) (k : PPair) :
    (makeCram b ds a).atPair k=cramer b (select (middleBase b ds) a) k := by cases k <;> rfl

def occurrence : Nat→Option PPair
  | 140 | 141 => some .one
  | 158 | 159 => some .two
  | 170 | 171 => some .three
  | 182 | 183 => some .four
  | _ => none

def admissible (r : Nat×Polynomial) : Bool := match occurrence r.1 with
  | none => reads (apart padeSlots) r.2
  | some k => blindLine k.slot r.2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
theorem active_admissible (g : Bool) : ∀r∈activeRows g, admissible r=true := by
  have h : (activeRows g).all admissible=true := by cases g <;> decide
  exact List.all_eq_true.mp h

def dressed (b : Book) (l : Aff) (t : Triple) :=
  plus b (times b t.d l.c) (plus b (times b l.u t.u) (times b l.v t.v))

def numerator (b : Book) (env : Coords) (cs : CramTable) (r : Nat×Polynomial) : Word :=
  match occurrence r.1 with
  | none => (clearRow b env r.2).num
  | some k => dressed b (line b env k.slot r.2) (cs.atPair k)

def rowFactor (b : Book) (x : ProjectionDescent.Assignment) (env : Coords) (cs : CramTable) (r : Nat×Polynomial) : Rat :=
  match occurrence r.1 with
  | none => (common env r.2:Rat)
  | some k => (cs.atPair k).d.value b x*(line b env k.slot r.2).den

theorem every_residual {b env g} (y : Fin 130→Rat) (al : Along b (finiteLift y) env (middle g y))
    (cs : CramTable) (hc : ∀k,CramerCorrect b (finiteLift y) (chartPoint g y) k (cs.atPair k))
    (r : Nat×Polynomial) (hr : r∈activeRows g) :
    rowFactor b (finiteLift y) env cs r≠0 ∧
    (numerator b env cs r).value b (finiteLift y)=rowFactor b (finiteLift y) env cs r*value (chartPoint g y) r.2 := by
  have h:=active_admissible g r hr
  have offZ : off padeSlots (middle g y) (chartPoint g y) := fun _ hi=>fillPairs_keep _ hi
  cases e:occurrence r.1 with
  | none =>
    have blind : reads (apart padeSlots) r.2=true := by simpa [admissible,e] using h
    have eq:=agree_off offZ _ (reads_supported blind)
    have ch:=clear_row_value al r.2
    simp only [rowFactor,numerator,e,eq]
    exact ⟨rat_den_ne _ ch.1,ch.2⟩
  | some k =>
    have blind : blindLine k.slot r.2=true := by simpa [admissible,e] using h
    have lhs:=line_correct al k.slot r.2;have rhs:=hc k
    simp only [rowFactor,numerator,e,dressed,plus_value,times_value]
    refine ⟨fun eq=>rat_den_ne _ lhs.pos ((Rat.mul_eq_zero.mp eq).resolve_left rhs.nonzero),?_⟩
    rw [rhs.u,rhs.v,lhs.u,lhs.v,lhs.c,placement blind offZ];grobner

def lowRows (g : Bool) : Rows :=
  ((activeRows g).filter (fun r => !peakIds.contains r.1)).mergeSort (fun a b=>decide (a.1≤b.1))

def highWords (b : Book) (g : Bool) (env : Coords) (cs : CramTable) :=
  (peakRows g).map (numerator b env cs)

def lowWords (b : Book) (g : Bool) (env : Coords) (ds : DetTable) (cs : CramTable) :=
  (lowRows g).map (numerator b env cs) ++ detectors.map (fun k=>(ds.atBlock k).guard)

def combineSums (b : Book) (high low : List Word) : Outputs :=
  let h:=squares b (integer b 0) high
  let l:=squares b (integer b 0) low
  let X:=varWord b 1
  ⟨plus b h l,plus b h (times b (times b X X) l)⟩

@[noinline] def finishTable (b : Book) (g : Bool) (ds : DetTable) (a : Array (Option Cell)) (cs : CramTable) : Outputs :=
  let env:=select (middleBase b ds) a
  combineSums b (highWords b g env cs) (lowWords b g env ds cs)

@[noinline] def finishMiddle (b : Book) (g : Bool) (ds : DetTable) (a : Array (Option Cell)) : Outputs :=
  finishTable b g ds a (makeCram b ds a)

@[noinline] def finishDetector (b : Book) (g : Bool) (ds : DetTable) : Outputs :=
  finishMiddle b g ds (cells b (ps g) (middleBase b ds))

def outputs130 (b : Book) (g : Bool) : Outputs := finishDetector b g (detTable b g)
end Physical130
