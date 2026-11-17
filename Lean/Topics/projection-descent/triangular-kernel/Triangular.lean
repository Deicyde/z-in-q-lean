import ProjectionSupport
namespace Triangular
open ZeroInput.Sparse ProjectionDescent

structure Pivot where
  id : Nat
  slot : Nat
  lead : Int
  pre : Polynomial
  post : Polynomial

def Pivot.row (p : Pivot) : Polynomial := p.pre ++ [⟨p.lead,[p.slot]⟩] ++ p.post
def Pivot.num (p : Pivot) := scale (-1) (p.pre++p.post)
def Pivot.sol (p : Pivot) (x : Assignment) := value x p.num / (p.lead:Rat)
def Pivot.ok (p : Pivot) (x : Assignment) : Prop := (p.lead:Rat)*x p.slot=value x p.num

def slots (ps : List Pivot) := ps.map Pivot.slot

def recov : List Pivot → Assignment → Assignment
  | [], x => x
  | p::ps, x => recov ps (put x p.slot (p.sol x))

def valid : List Pivot → Bool
  | [] => true
  | p::ps => decide (p.lead≠0 ∧ p.slot∉slots ps) && reads (apart (p.slot::slots ps)) p.num && valid ps

theorem keeps (ps : List Pivot) (x : Assignment) : off (slots ps) x (recov ps x) := by
  induction ps generalizing x with
  | nil => intro i _; rfl
  | cons p ps ih =>
    intro i hi
    have h : i≠p.slot ∧ i∉slots ps := by simpa [slots] using hi
    change recov ps (put x p.slot (p.sol x)) i=x i
    rw [ih _ i h.2]; simp [put,h.1]

private theorem splitValid {p : Pivot} {ps : List Pivot} (hv : valid (p::ps)=true) :
    (p.lead≠0 ∧ p.slot∉slots ps) ∧ reads (apart (p.slot::slots ps)) p.num=true ∧ valid ps=true := by
  simpa [valid,and_assoc] using hv

theorem all_solved (ps : List Pivot) (hv : valid ps=true) (x : Assignment) :
    ∀ p∈ps, p.ok (recov ps x) := by
  induction ps generalizing x with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨⟨nz,fresh⟩,sup,tail⟩ := splitValid hv
    let y := put x p.slot (p.sol x)
    have offX := keeps (p::ps) x
    have n := agree_off offX p.num (reads_supported sup)
    intro q mem
    rcases List.mem_cons.mp mem with eq|h
    · subst q; unfold Pivot.ok
      change _ * recov ps y p.slot = _
      rw [keeps ps y p.slot fresh,n]
      have clear : p.sol x*(p.lead:Rat)=value x p.num := Rat.div_mul_cancel (fun h => nz (Rat.intCast_eq_zero_iff.mp h))
      simp [y,put]; grobner
    · exact ih tail y q h

theorem recov_eq (ps : List Pivot) (hv : valid ps=true) (x y : Assignment)
    (eq : off (slots ps) x y) : recov ps x=recov ps y := by
  induction ps generalizing x y with
  | nil => funext i; exact (eq i (by simp [slots])).symm
  | cons p ps ih =>
    obtain ⟨_,sup,tail⟩ := splitValid hv
    have n := agree_off eq p.num (reads_supported sup)
    apply ih tail
    intro i outside; by_cases h : i=p.slot
    · subst i; simp [put,Pivot.sol,n]
    · simp [put,h]; exact eq i (by simp [slots,h] at *; assumption)

theorem fixed (ps : List Pivot) (hv : valid ps=true) (x : Assignment) (ok : ∀ p∈ps,p.ok x) : recov ps x=x := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨⟨nz,_⟩,_,tail⟩ := splitValid hv
    have e := ok p (by simp); unfold Pivot.ok at e
    have cnz : (p.lead:Rat)≠0 := fun h => nz (Rat.intCast_eq_zero_iff.mp h)
    have clear : p.sol x*(p.lead:Rat)=value x p.num := Rat.div_mul_cancel cnz
    have val : p.sol x=x p.slot := by grind
    have restore : put x p.slot (p.sol x)=x := by funext i; by_cases h : i=p.slot <;> simp [put,h,val]
    change recov ps (put x p.slot (p.sol x))=x
    rw [restore]; exact ih tail (fun q h => ok q (List.mem_cons_of_mem _ h))

def parent (ps : List Pivot) (remain : Rows) : Rows :=
  ((ps.map (fun p => (p.id,p.row)))++remain).mergeSort (fun a b => decide (a.1≤b.1))

theorem parent_clause (ps : List Pivot) (rs : Rows) (x : Assignment) :
    (∀ r∈parent ps rs, value x r.2=0) ↔ (∀ p∈ps,p.ok x) ∧ (∀ r∈rs,value x r.2=0) := by
  have cell (p : Pivot) : value x p.row=0 ↔ p.ok x := pivot_cell p.pre p.post p.slot p.lead x
  constructor
  · intro old; constructor
    · intro p h; apply (cell p).mp; apply old (p.id,p.row); apply List.mem_mergeSort.mpr
      exact List.mem_append_left _ (List.mem_map.mpr ⟨p,h,rfl⟩)
    · intro r h; exact old r (List.mem_mergeSort.mpr (List.mem_append_right _ h))
  · rintro ⟨a,b⟩ r mem
    rcases List.mem_append.mp (List.mem_mergeSort.mp mem) with h|h
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h; exact (cell p).mpr (a p hp)
    · exact b r h

def inside (i : Nat) := decide (1≤i ∧ i≤226)
def seed (code : Nat→Nat) (y : Fin 153→Rat) (i : Nat) : Rat := if inside i then finiteLift y (code i) else 0

theorem finite_at {n} (y : Fin n→Rat) {i} (lo : 1≤i) (hi : i≤n) :
    finiteLift y i=y ⟨i-1,by omega⟩ := by cases i with | zero => omega | succ i => simp [finiteLift,show i<n by omega]

theorem finite_out {n} (y : Fin n→Rat) {i} (bad : ¬(1≤i ∧ i≤n)) : finiteLift y i=0 := by
  cases i with | zero => rfl | succ i => simp [finiteLift,show ¬i<n by omega]

theorem trunc (x : Assignment) (outside : ∀ i,inside i=false→x i=0) : ∃ a : Fin 226→Rat, finiteLift a=x := by
  refine ⟨fun i => x (i.val+1),?_⟩;funext i
  by_cases ok : 1≤i ∧ i≤226
  · rw [finite_at _ ok.1 ok.2]; change x (i-1+1)=x i; rw [show i-1+1=i by omega]
  · rw [finite_out _ ok,outside _ (by simp [inside,ok])]

def ordinary (ps : List Pivot) (rs : Rows) (code : Nat→Nat) (y : Fin 153→Rat) :=
  RowSquares.sumSquares (recov ps (seed code y)) rs

theorem ordinary_iff (ps : List Pivot) (rs : Rows) (code back : Nat→Nat) (a : Rat)
    (hv : valid ps=true) (input : 1∉slots ps) (c1 : code 1=1) (b1 : back 1=1)
    (inRange : ∀ i∈slots ps, inside i=true)
    (ranks : ∀ i, inside i=true → i∉slots ps → 1≤code i ∧ code i≤153 ∧ back (code i)=i) :
    RowsProject 226 (parent ps rs) a ↔ ∃ y : Fin 153→Rat, finiteLift y 1=a ∧ ordinary ps rs code y=0 := by
  have gram (x : Assignment) : RowSquares.sumSquares x rs=0 ↔ ∀ r∈rs, value x r.2=0 := by
    rw [←RowSquares.expansion_value]; exact RowSquares.zero_iff_rows _ _
  constructor
  · rintro ⟨x,hx,hs⟩
    obtain ⟨hp,hr⟩ := (parent_clause _ _ _).mp hs
    let y (i : Fin 153) := finiteLift x (back (i.val+1))
    have fy {i : Nat} (lo : 1≤i) (hi : i≤153) : finiteLift y i=finiteLift x (back i) := by
      rw [finite_at _ lo hi]; change finiteLift x (back (i-1+1))=_; rw [show i-1+1=i by omega]
    have offP : off (slots ps) (finiteLift x) (seed code y) := by
      intro i outside;by_cases h : inside i=true
      · obtain ⟨lo,hi,inv⟩ := ranks i h outside; simp [seed,h,fy lo hi,inv]
      · have ext : ¬(1≤i ∧ i≤226) := by simpa [inside] using h
        simp [seed,h,finite_out x ext]
    refine ⟨y,by rw [fy (by decide) (by decide),b1,hx],?_⟩
    change RowSquares.sumSquares (recov ps (seed code y)) rs=0
    rw [←recov_eq ps hv (finiteLift x) _ offP,fixed ps hv _ hp]; exact (gram _).mpr hr
  · rintro ⟨y,hy,sol⟩
    let x := recov ps (seed code y)
    have offR := keeps ps (seed code y)
    have out (i : Nat) (h : inside i=false) : x i=0 := by
      have away : i∉slots ps := fun m => by have := inRange i m; simp [h] at this
      rw [show x i=seed code y i from offR i away]; simp [seed,h]
    obtain ⟨v,eq⟩ := trunc x out
    refine ⟨v,?_,?_⟩
    · rw [eq,show x 1=seed code y 1 from offR 1 input]; simpa [seed,inside,c1] using hy
    · rw [eq]; apply (parent_clause _ _ _).mpr; exact ⟨all_solved ps hv _,(gram x).mp sol⟩



def marked (ps : List Pivot) (top : Nat×Polynomial) (rs : Rows) (code : Nat→Nat) (y : Fin 153→Rat) :=
  let x := recov ps (seed code y)
  (value x top.2)^2+(finiteLift y 1)^2*RowSquares.sumSquares x rs

private theorem sq_nonneg (x : Rat) : 0≤x*x := by
  by_cases h : 0≤x
  · exact Rat.mul_nonneg h h
  · have ne : 0≤ -x := by grind
    have pos := Rat.mul_nonneg ne ne; grind

private theorem sum_nonneg (x : Assignment) (r : Rows) : 0≤RowSquares.sumSquares x r := by
  induction r with
  | nil => exact Rat.le_refl
  | cons h t ih => exact Rat.add_nonneg (sq_nonneg _) ih

private theorem nz_iff (ps : List Pivot) (top : Nat×Polynomial) (rs : Rows) (code : Nat→Nat)
    (y : Fin 153→Rat) (nz : finiteLift y 1≠0) :
    marked ps top rs code y=0 ↔ ordinary ps (top::rs) code y=0 := by
  let x := recov ps (seed code y)
  let A := value x top.2
  let B := RowSquares.sumSquares x rs
  let X := finiteLift y 1
  have hA := sq_nonneg A; have hB : 0≤B := sum_nonneg _ _
  have hC := Rat.mul_nonneg (sq_nonneg X) hB
  change A^2+X^2*B=0 ↔ A*A+B=0
  constructor
  · intro h; have za : A*A=0 := by grind
    have zc : X*(X*B)=0 := by grobner
    have zb := (Rat.mul_eq_zero.mp ((Rat.mul_eq_zero.mp zc).resolve_left nz)).resolve_left nz
    rw [za,zb]; grobner
  · intro h; have za : A*A=0 := by grind
    have zb : B=0 := by grind
    grobner

theorem marked_iff (ps : List Pivot) (top : Nat×Polynomial) (rs : Rows) (code : Nat→Nat) (a : Rat)
    (ord : RowsProject 226 (parent ps (top::rs)) a ↔ ∃ y,finiteLift y 1=a ∧ ordinary ps (top::rs) code y=0)
    (zero : ∃ y,finiteLift y 1=0 ∧ ordinary ps [top] code y=0) :
    (∃ y,finiteLift y 1=a ∧ marked ps top rs code y=0) ↔ RowsProject 226 (parent ps (top::rs)) a ∨ a=0 := by
  by_cases ha : a=0
  · subst a
    obtain ⟨y,hy,q⟩ := zero
    let x := recov ps (seed code y)
    change value x top.2*value x top.2+0=0 at q
    exact ⟨fun _ => Or.inr rfl,fun _ => ⟨y,hy,by change (value x top.2)^2+(finiteLift y 1)^2*_=0; rw [hy]; grobner⟩⟩
  · constructor
    · rintro ⟨y,hy,q⟩; left; apply ord.mpr
      exact ⟨y,hy,(nz_iff _ _ _ _ _ (hy ▸ ha)).mp q⟩
    · intro h; obtain ⟨y,hy,q⟩ := ord.mp (h.resolve_right ha)
      exact ⟨y,hy,(nz_iff _ _ _ _ _ (hy ▸ ha)).mpr q⟩

def intMon (v : Nat→Int) : List Nat → Int
  | [] => 1 | i::m => v i*intMon v m

def intVal (v : Nat→Int) : Polynomial → Int
  | [] => 0 | t::ts => t.coefficient*intMon v t.monomial+intVal v ts

theorem int_value (v : Nat→Int) (p : Polynomial) : (intVal v p : Rat)=value (fun i => (v i : Rat)) p := by
  have mon (m : List Nat) : (intMon v m : Rat)=monomialValue (fun i => (v i : Rat)) m := by
    induction m with
    | nil => rfl
    | cons i m ih => simp only [intMon,monomialValue,Rat.intCast_mul,ih]
  induction p with
  | nil => rfl
  | cons h t ih => simp only [intVal,value,termValue,Rat.intCast_add,Rat.intCast_mul,mon,ih]

theorem zero_parent (ps : List Pivot) (top : Nat×Polynomial) (v : Nat→Int)
    (small : ∀ i,inside i=false → v i=0) (inp : v 1=0)
    (piv : ps.all (fun p => decide (intVal v p.row=0))=true) (endRow : intVal v top.2=0) :
    RowsProject 226 (parent ps [top]) 0 := by
  obtain ⟨x,eq⟩ := trunc (fun i => (v i:Rat)) (fun i h => by change (v i:Rat)=0; rw [small i h]; rfl)
  refine ⟨x,by rw [eq]; change (v 1:Rat)=0; rw [inp]; rfl,?_⟩
  rw [eq]; apply (parent_clause _ _ _).mpr
  constructor
  · intro p hp; apply (pivot_cell p.pre p.post p.slot p.lead (fun i => (v i:Rat))).mp
    change value _ p.row=0
    have h := of_decide_eq_true (List.all_eq_true.mp piv p hp)
    rw [←int_value,h]; rfl
  · intro r h; have same : r=top := by simpa using h
    subst r; rw [←int_value,endRow]; rfl

end Triangular
