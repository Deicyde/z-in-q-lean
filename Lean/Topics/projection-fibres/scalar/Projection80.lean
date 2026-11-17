import Layout80

namespace ProjectionFibres.Actual
open StructuralReduction StructuralReduction.Transfer84
set_option maxRecDepth 10000

def withGuard (B : Base) (g : Rat) : Data where
  L := (r (empty B))^16
  C := (r (empty B))^3
  A := A (empty B)
  guard := g
  kappa := Wires.kappa
  t := cell (empty B) 18
  s := cell (empty B) 19
  j := cell (empty B) 20
  z := cell (empty B) 23
  w := cell (empty B) 24
  other := fun a b=>∀ n∈retained,wire (fill B a b 0 0 0 0) n=0

abbrev data (B : Base) := withGuard B (fixed B 9915)

private theorem guard_field (B : Base) (g : Rat) : (withGuard B g).guard=g := rfl

private theorem data_guard (B : Base) : (data B).guard=fixed B 9915 :=
  guard_field B (fixed B 9915)

private theorem split_rows (w : Nat→Rat) :
    (∀ j∈Output.wireList,w j=0) ↔ w 513=0 ∧ (∀ j∈retained,w j=0) ∧
      w 1072=0 ∧ w 1038=0 ∧ w 113=0 ∧ w 883=0 ∧ w 9917=0 := by
  have perm : Output.wireList.Perm ([513,1072,1038,113,883,9917]++retained) := by decide
  simp only [perm.mem_iff,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · intro h
    exact ⟨h _ (by simp),fun j m=>h j (Or.inr m),h _ (by simp),h _ (by simp),h _ (by simp),h _ (by simp),h _ (by simp)⟩
  · rintro ⟨c,other,a,b,d,e,f⟩ j m
    rcases m with (rfl|rfl|rfl|rfl|rfl|rfl)|mem <;> first | assumption | exact other j mem

private theorem guard_change (v i j d g : Rat) (row : v=i*d-1) (left : i=j)
    (right : d=g) : v=j*g-1 := by rw [row,left,right]

private theorem sub_one (t : Rat) : t-1=0 ↔ t=1 := by constructor <;> intro h <;> grobner

theorem normal_form (B : Base) (a b d m v i : Rat) :
    output false (fill B a b d m v i)=0 ↔ OldPoint (data B) a b d m v i := by
  let x:=fill B a b d m v i
  have shape := ((signed84 archiveAt x).1).trans (split_rows (wire x))
  change (output false x=0 ↔ _)
  rw [show (output false x=0) ↔ _ from shape]
  have others : (∀j∈retained,wire x j=0) ↔ (data B).other a b := by
    constructor <;> intro good j hj
    · exact (retained_agree B a b d m v i hj).symm.trans (good j hj)
    · exact (retained_agree B a b d m v i hj).trans (good j hj)
  have curveEq : wire x 513=curve a b (data B).z (data B).w := curve_row x
  have numEq : wire x 1072=0 ↔ d*(data B).L=(data B).A := equation_num x
  have recEq : wire x 1038=0 ↔ m*d*(data B).L=d^2+(data B).C*(qnorm a b)^2 := equation_rec x
  have corrEq : wire x 113=0 ↔ m^2=(data B).kappa*v*(data B).C := equation_corr x
  have poleEq : wire x 883=pole (data B).t (data B).s (data B).j ((data B).kappa*v) := equation_pole x
  have hg : wire x 9915=fixed B 9915 := base_guard B a b d m v i
  have hg2 : wire x 9915=(data B).guard := by rw [data_guard];exact hg
  have hi : cell x 84=i := rfl
  have invEq := guard_change (wire x 9917) (cell x 84) i (wire x 9915) ((data B).guard) (guard_row x) hi hg2
  rw [curveEq,others,numEq,recEq,corrEq,poleEq,invEq,sub_one]
  constructor
  · rintro ⟨c,o,n,t,h,s,g⟩
    exact ⟨c,o,n,t,h,s,g⟩
  · intro p
    exact ⟨p.curveEq,p.others,p.num,p.reciprocal,p.corr,p.sextic,p.inverse⟩

def squares : List Rat→Rat
  | []=>0
  | v::vs=>v^2+squares vs

private theorem sum_test (xs : List Rat) :
    0≤squares xs ∧ (squares xs=0 ↔ ∀v∈xs,v=0) := by
  induction xs with
  | nil => simp [squares] <;> decide
  | cons v vs ih =>
    have sq : 0≤v^2 := by
      rcases Rat.nonneg_total v with h|h
      · exact Rat.pow_nonneg h
      · have nn:=Rat.mul_nonneg h h
        rwa [show -v*(-v)=v^2 by grobner] at nn
    have tail:=ih.1
    change 0≤v^2+squares vs ∧ _
    refine ⟨by grind,?_⟩
    constructor
    · intro zero
      change v^2+squares vs=0 at zero
      have e : v^2=0 := by grind
      have t : squares vs=0 := by grind
      intro k hk
      obtain rfl|mem:=List.mem_cons.mp hk
      · have prod : k*k=0 := by grobner
        exact (Rat.mul_eq_zero.mp prod).elim id id
      · exact ih.2.mp t k mem
    · intro good
      have e:=good v (by simp)
      have t:=ih.2.mpr (fun k h=>good k (List.mem_cons_of_mem _ h))
      simp [squares,e,t] <;> grobner

def reducedRows (B : Base) (x y : Rat) : List Rat :=
  let f:=data B
  let a:=f.h*x
  let b:=f.h*y
  curve a b f.z f.w :: homogeneousPole f.t f.s f.j (f.N (qnorm a b)) f.D ::
    retained.map (wire (fill B a b 0 0 0 0))

theorem reduced_iff (B : Base) (x y : Rat) :
    squares (reducedRows B x y)=0 ↔ NewPoint (data B) x y := by
  rw [(sum_test _).2]
  simp only [reducedRows,List.mem_cons,List.mem_map]
  constructor
  · intro h
    exact ⟨h _ (Or.inl rfl),fun j mem=>h _ (Or.inr (Or.inr ⟨j,mem,rfl⟩)),h _ (Or.inr (Or.inl rfl))⟩
  · rintro ⟨c,o,s⟩ k (rfl|rfl|⟨j,hj,rfl⟩)
    · exact c
    · exact s
    · exact o j hj

def base80 (v : Fin 80→Rat) : Base := fun k=>v ⟨k.val,by omega⟩
def pack80 (B : Base) (x y : Rat) (k : Fin 80) : Rat :=
  if h : k.val<78 then B ⟨k.val,h⟩ else if k.val=78 then x else y

/-- The ordinary polynomial in eighty variables and its input-marked companion. -/
def ordinary80 (v : Fin 80→Rat) : Rat := squares (reducedRows (base80 v) (v 78) (v 79))

def output80 : Bool → (Fin 80→Rat) → Rat
  | false, v => ordinary80 v
  | true, v => v 0*ordinary80 v

private theorem regular (B : Base) :
    (data B).L≠0 ∧ (data B).C≠0 ∧ (data B).kappa≠0 := by
  have pos:=r_positive (empty B)
  have nz : r (empty B)≠0 := by grind
  exact ⟨by change (r (empty B))^16≠0;grind,
         by change (r (empty B))^3≠0;grind,by change Wires.kappa≠0;decide⟩

/-- Ordinary fibres above all 78 fixed coordinates, for arbitrary rational values. -/
theorem base_fibres (B : Base) :
    (∃ a b d m v i, output false (fill B a b d m v i)=0) ↔
    ∃ x y,squares (reducedRows B x y)=0 := by
  simp only [normal_form,reduced_iff]
  exact fibres_iff _ (regular B).1 (regular B).2.1 (regular B).2.2

private theorem pack_base (B : Base) (x y : Rat) : base80 (pack80 B x y)=B := by
  funext j
  simp [base80,pack80,j.isLt]

private theorem pack_eval (B : Base) (s t : Rat) :
    output80 false (pack80 B s t)=squares (reducedRows B s t) := by
  change squares (reducedRows (base80 (pack80 B s t)) s t)=_
  rw [pack_base]

private theorem ordinary_eval (y : Fin 80→Rat) :
    output80 false y=squares (reducedRows (base80 y) (y 78) (y 79)) := rfl

private theorem marked80 (y : Fin 80→Rat) : output80 true y=y 0*output80 false y := rfl

private theorem marked84 (x : Fin 84→Rat) :
    output true x=0 ↔ cell x 1=0 ∨ output false x=0 := by
  have h:=signed84 archiveAt x
  exact h.2.trans (or_congr_right h.1.symm)

theorem ordinary_projection (T : Rat) :
    (∃ x : Fin 84→Rat,cell x 1=T ∧ output false x=0) ↔
    ∃ y : Fin 80→Rat,y 0=T ∧ output80 false y=0 := by
  constructor
  · rintro ⟨x,input,zero⟩
    obtain ⟨B,a,b,d,m,v,i,rfl⟩:=decompose x
    obtain ⟨s,t,h⟩:=(base_fibres B).mp ⟨a,b,d,m,v,i,zero⟩
    refine ⟨pack80 B s t,input,?_⟩
    exact (pack_eval B s t).trans h
  · rintro ⟨y,input,zero⟩
    obtain ⟨a,b,d,m,v,i,h⟩:=(base_fibres (base80 y)).mpr ⟨y 78,y 79,(ordinary_eval y).symm.trans zero⟩
    exact ⟨fill (base80 y) a b d m v i,input,h⟩

theorem projection_iff (mark : Bool) (T : Rat) :
    (∃ x : Fin 84→Rat,cell x 1=T ∧ output mark x=0) ↔
    ∃ y : Fin 80→Rat,y 0=T ∧ output80 mark y=0 := by
  cases mark with
  | false => exact ordinary_projection T
  | true =>
    by_cases z : T=0
    · subst T
      exact iff_of_true ⟨fun _=>0,rfl,(marked84 _).mpr (Or.inl rfl)⟩
        ⟨fun _=>0,rfl,(marked80 _).trans (Rat.zero_mul _)⟩
    · constructor
      · rintro ⟨x,input,zero⟩
        have all:=((marked84 x).mp zero).resolve_left (fun h=>z (input.symm.trans h))
        obtain ⟨y,i,ordinary⟩:=(ordinary_projection T).mp ⟨x,input,all⟩
        exact ⟨y,i,by rw [marked80,ordinary,Rat.mul_zero]⟩
      · rintro ⟨y,input,zero⟩
        rw [marked80] at zero
        have ordinary:=(Rat.mul_eq_zero.mp zero).resolve_left (fun h=>z (input.symm.trans h))
        obtain ⟨x,i,o⟩:=(ordinary_projection T).mpr ⟨y,input,ordinary⟩
        exact ⟨x,i,(marked84 x).mpr (Or.inr o)⟩

#print axioms normal_form
#print axioms base_fibres
#print axioms projection_iff
end ProjectionFibres.Actual
