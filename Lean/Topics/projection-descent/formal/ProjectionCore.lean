import RowSquares

namespace ProjectionDescent
open ZeroInput.Sparse
open Lean.Grind

abbrev Polynomial := List Term
abbrev Rows := List (Nat × Polynomial)
abbrev Assignment := Nat → Rat
abbrev Family := Nat → Polynomial

def RowsProject (n : Nat) (rows : Rows) (a : Rat) : Prop :=
  ∃ x : Fin n → Rat, finiteLift x 1=a ∧ ∀ r ∈ rows, value (finiteLift x) r.2=0

def holds (I : List Nat) (f : Family) (x : Assignment) : Prop := ∀ i ∈ I, value x (f i)=0

def project (I : List Nat) (f : Family) (a : Rat) : Prop := ∃ x : Assignment, x 1=a ∧ holds I f x

def put (x : Assignment) (j : Nat) (v : Rat) : Assignment := fun i => if i=j then v else x i

def scale (c : Int) (p : Polynomial) : Polynomial := p.map fun t => ⟨c*t.coefficient,t.monomial⟩

theorem scale_value (x : Assignment) (c : Int) (p : Polynomial) :
    value x (scale c p) = (c:Rat)*value x p := by
  induction p with
  | nil => simp [scale,value]
  | cons t ts ih =>
    change termValue x ⟨c*t.coefficient,t.monomial⟩+value x (scale c ts) = _
    rw [ih]; simp only [value,termValue,Rat.intCast_mul]; grobner

deriving instance DecidableEq for ZeroInput.Sparse.Term

def content (p : Polynomial) : Nat := p.foldl (fun g t => g.gcd t.coefficient.natAbs) 0

-- A candidate divisor is accepted only when scaling back recovers every signed term.
def primitive (p : Polynomial) : Polynomial :=
  let t := RowSquares.collect p
  let g : Int := content t
  let q : Polynomial := t.map fun u => ⟨u.coefficient / g,u.monomial⟩
  if g≠0 ∧ scale g q=t then q else t

theorem primitive_value (p : Polynomial) :
    ∃ g : Rat, g≠0 ∧ ∀ x, g*value x (primitive p)=value x p := by
  let t := RowSquares.collect p
  let g : Int := content t
  let q : Polynomial := t.map fun u => ⟨u.coefficient/g,u.monomial⟩
  by_cases ok : g≠0 ∧ scale g q=t
  · have hp : primitive p=q := if_pos ok
    refine ⟨(content (RowSquares.collect p):Int),?_,?_⟩
    · exact fun h => ok.1 (Rat.intCast_eq_zero_iff.mp h)
    · intro x; rw [hp]; change (g:Rat)*value x q = _; rw [←scale_value,ok.2]; exact RowSquares.collect_value _ _
  · have hp : primitive p=t := if_neg ok
    exact ⟨1,by decide,fun x => by rw [hp,Rat.one_mul]; exact RowSquares.collect_value _ _⟩

def countSlot (j : Nat) : List Nat → Nat
  | [] => 0
  | i::rest => if i=j then countSlot j rest+1 else countSlot j rest

def width (j : Nat) : Polynomial → Nat
  | [] => 0
  | t::r => max (countSlot j t.monomial) (width j r)

def imageMonomial (j : Nat) (num : Polynomial) : List Nat → Polynomial
  | [] => [⟨1,[]⟩]
  | i::rest => RowSquares.product (if i=j then num else [⟨1,[i]⟩]) (imageMonomial j num rest)

private theorem image_value (x : Assignment) (j : Nat) (num : Polynomial) (v c : Rat)
    (root : v*c=value x num) (m : List Nat) :
    value x (imageMonomial j num m)=monomialValue (put x j v) m*c^(countSlot j m) := by
  induction m with
  | nil => simp [imageMonomial,countSlot,value,termValue,monomialValue,Rat.add_zero]
  | cons i m ih =>
    by_cases e : i=j
    · subst i
      simp [imageMonomial,RowSquares.product_value,ih,←root,countSlot,monomialValue,put,Rat.pow_succ]
      grobner
    · simp only [imageMonomial,if_neg e,RowSquares.product_value,ih,countSlot,monomialValue,put,
        value,termValue,Rat.intCast_one,Rat.mul_one,Rat.one_mul,Rat.add_zero]
      grobner

def substituteAt (j degree : Nat) (c : Int) (num : Polynomial) (p : Polynomial) : Polynomial :=
  p.flatMap fun t => scale (t.coefficient*c^(degree-countSlot j t.monomial))
    (imageMonomial j num t.monomial)

private theorem substituteAt_value (j k : Nat) (c : Int) (num p : Polynomial) (x : Assignment)
    (v : Rat) (root : v*(c:Rat)=value x num) (bound : width j p ≤ k) :
    value x (substituteAt j k c num p)= (c:Rat)^k*value (put x j v) p := by
  induction p with
  | nil => simp [substituteAt,value]
  | cons t r ih =>
    have le : countSlot j t.monomial≤k := by change max _ _ ≤ _ at bound; omega
    have tail : width j r≤k := by change max _ _ ≤ _ at bound; omega
    have powers : (c:Rat)^(k-countSlot j t.monomial)*(c:Rat)^(countSlot j t.monomial)=(c:Rat)^k := by
      rw [←Semiring.pow_add,show k-countSlot j t.monomial+countSlot j t.monomial=k by omega]
    change value x (scale _ (imageMonomial j num t.monomial) ++ substituteAt j k c num r)=_
    rw [value_append,scale_value,ih tail,image_value x j num v c root]
    simp only [Rat.intCast_mul,Rat.intCast_pow,value,termValue]
    grobner

private theorem monomial_unchanged (x : Assignment) (j : Nat) (v : Rat) (m : List Nat)
    (zero : countSlot j m=0) : monomialValue (put x j v) m=monomialValue x m := by
  induction m with
  | nil => rfl
  | cons i m ih =>
    by_cases h : i=j
    · subst i; simp [countSlot] at zero
    · simp only [countSlot,if_neg h] at zero
      simp only [monomialValue,put,if_neg h,ih zero]

theorem unchanged (x : Assignment) (j : Nat) (v : Rat) (r : Polynomial)
    (zero : width j r=0) : value (put x j v) r = value x r := by
  induction r with
  | nil => rfl
  | cons t r ih =>
    change max _ _=0 at zero
    have head : countSlot j t.monomial=0 := by omega
    have tail : width j r=0 := by omega
    simp only [value,termValue,monomial_unchanged x j v _ head,ih tail]

def substitute (j : Nat) (c : Int) (num p : Polynomial) : Polynomial :=
  let k := width j p
  if k=0 then p else primitive (substituteAt j k c num p)

/-- Every compiled row is its original row on the lifted assignment, up to a fixed nonzero scalar. -/
theorem substitute_value (j : Nat) (c : Int) (hc : c≠0) (num p : Polynomial) :
    ∃ k : Rat, k≠0 ∧ ∀ x : Assignment, value x (substitute j c num p) =
      k*value (put x j (value x num/(c:Rat))) p := by
  have hc' : (c:Rat)≠0 := fun h => hc (Rat.intCast_eq_zero_iff.mp h)
  by_cases h : width j p=0
  · rw [show substitute j c num p=p from if_pos h]
    exact ⟨1,by decide,fun x => by rw [Rat.one_mul,unchanged _ _ _ _ h]⟩
  · rw [show substitute j c num p=primitive (substituteAt j (width j p) c num p) from if_neg h]
    let exponent := width j p
    obtain ⟨g,hg,e⟩ := primitive_value (substituteAt j exponent c num p)
    let k : Rat := (c:Rat)^exponent/g
    have kg : k*g=(c:Rat)^exponent := Rat.div_mul_cancel hg
    have powNZ : (c:Rat)^exponent≠0 := by
      induction exponent with
      | zero => simp
      | succ n h => rw [Rat.pow_succ]; exact fun z => (Rat.mul_eq_zero.mp z).elim h hc'
    refine ⟨k,fun zero => powNZ (by rw [zero] at kg; grind),?_⟩
    intro x
    have ev := substituteAt_value j exponent c num p x (value x num/(c:Rat)) (Rat.div_mul_cancel hc') (Nat.le_refl _)
    have step := (e x).trans ev
    change value x (primitive (substituteAt j exponent c num p)) = _
    have cancelG {u b : Rat} (eq : u*g=b*g) : u=b := by grind
    apply cancelG
    calc value x (primitive (substituteAt j exponent c num p))*g = g*value x (primitive (substituteAt j exponent c num p)) := by grobner
         _ = _ := by rw [step,←kg]; grobner


def reads (live : Nat → Bool) (p : Polynomial) : Bool := p.all fun t => t.monomial.all live

def supported (live : Nat → Bool) (p : Polynomial) : Prop :=
  ∀ x y : Assignment, (∀ i, live i=true → x i=y i) → value x p=value y p

theorem reads_supported {live p} (ok : reads live p=true) : supported live p := by
  intro x y same
  have mon (m : List Nat) (ok : m.all live=true) : monomialValue x m=monomialValue y m := by
    induction m with
    | nil => rfl
    | cons i is ih =>
      have h : live i=true ∧ is.all live=true := by simpa using ok
      simp only [monomialValue,same i h.1,ih h.2]
  induction p with
  | nil => rfl
  | cons t ts ih =>
    have parts : t.monomial.all live=true ∧ reads live ts=true := by simpa [reads] using ok
    obtain ⟨h,tail⟩ := parts
    simp only [value,termValue,mon t.monomial h,ih tail]

def dropSlot (live : Nat → Bool) (j i : Nat) := live i && decide (i≠j)

def removeId (p : Nat) (I : List Nat) := I.filter (· != p)

theorem subst_supported {live : Nat → Bool} {j : Nat} {c : Int} {num p : Polynomial}
    (hc : c≠0) (hnum : supported (dropSlot live j) num) (hold : supported live p) :
    supported (dropSlot live j) (substitute j c num p) := by
  obtain ⟨k,_,ev⟩ := substitute_value j c hc num p
  intro x y eq
  rw [ev,ev]
  apply congrArg (fun b : Rat => k*b)
  apply hold
  intro i hi
  by_cases h : i=j
  · subst i; simp [put,hnum x y eq]
  · simp only [put,if_neg h]; exact eq i (by simp [dropSlot,hi,h])

theorem subst_family {I : List Nat} {f : Family} {live : Nat → Bool} {j i : Nat} {c : Int}
    {num : Polynomial} (hc : c≠0) (hn : supported (dropSlot live j) num)
    (old : ∀ k∈I, supported live (f k)) :
    ∀ k∈removeId i I, supported (dropSlot live j) (substitute j c num (f k)) := by
  intro k mem
  exact subst_supported hc hn (old k (List.mem_filter.mp mem).1)

theorem pivot_cell (pre post : Polynomial) (j : Nat) (c : Int) (x : Assignment) :
    value x (pre ++ [⟨c,[j]⟩] ++ post)=0 ↔ (c:Rat)*x j=value x (scale (-1) (pre++post)) := by
  rw [value_append,value_append,scale_value,value_append]
  simp only [value,termValue,monomialValue,Rat.mul_one,Rat.add_zero,Rat.intCast_neg,Rat.intCast_one]; grind

/-- A constant pivot at a real table row gives both the forward and the unique reverse lift. -/
theorem pivot_project (I : List Nat) (f : Family) (rid j : Nat) (c : Int) (num : Polynomial)
    (hc : c≠0) (input : (1:Nat)≠j) (present : rid∈I) (free : width j num=0)
    (pivot : ∀ x : Assignment, value x (f rid)=0 ↔ (c:Rat)*x j=value x num) (a : Rat) :
    project I f a ↔ project (removeId rid I) (fun r => substitute j c num (f r)) a := by
  have hc' : (c:Rat)≠0 := fun h => hc (Rat.intCast_eq_zero_iff.mp h)
  constructor
  · rintro ⟨x,hx,old⟩
    have root := (pivot x).mp (old rid present)
    have eq : value x num/(c:Rat)=x j := by
      have div := Rat.div_mul_cancel (a:=value x num) hc'
      grind
    have restore : put x j (value x num/(c:Rat))=x := by
      funext i; by_cases h : i=j <;> simp [put,h,eq]
    refine ⟨x,hx,?_⟩
    intro r mem
    obtain ⟨k,_,ev⟩ := substitute_value j c hc num (f r)
    rw [ev,restore,old r (List.mem_filter.mp mem).1,Rat.mul_zero]
  · rintro ⟨x,hx,hnew⟩
    let v := value x num/(c:Rat)
    let y := put x j v
    have clear : v*(c:Rat)=value x num := Rat.div_mul_cancel hc'
    refine ⟨y,by simpa [y,put,input] using hx,?_⟩
    intro r mem
    by_cases h : r=rid
    · subst r; apply (pivot y).mpr
      change (c:Rat)*(put x j v j)=value (put x j v) num
      rw [unchanged x j v num free]; simp [put]; grobner
    · have newmem : r∈removeId rid I := List.mem_filter.mpr ⟨mem,by simpa using h⟩
      obtain ⟨k,knz,ev⟩ := substitute_value j c hc num (f r)
      have zero := hnew r newmem
      rw [ev] at zero
      exact (Rat.mul_eq_zero.mp zero).resolve_left knz

def renumber (code : Nat → Nat) (r : Polynomial) : Polynomial :=
  r.map fun t => ⟨t.coefficient,t.monomial.map code⟩

theorem renumber_value (code : Nat → Nat) (x : Assignment) (p : Polynomial) :
    value x (renumber code p)=value (fun i => x (code i)) p := by
  have mon (m : List Nat) : monomialValue x (m.map code)=monomialValue (fun i => x (code i)) m := by
    induction m with
    | nil => rfl
    | cons i is ih => simp only [List.map_cons,monomialValue,ih]
  induction p with
  | nil => rfl
  | cons t ts ih =>
    change _ + value x (renumber code ts)=_
    simp only [value,termValue,mon,ih]

def table (I : List Nat) (f : Family) : Rows := I.map fun i => (i,f i)

theorem table_holds (I : List Nat) (f : Family) (x : Assignment) :
    (∀ r∈table I f, value x r.2=0) ↔ holds I f x := by
  constructor
  · intro hs i h; exact hs (i,f i) (List.mem_map.mpr ⟨i,h,rfl⟩)
  · intro h r mem; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem; exact h i hi

/-- An injective renumbering on the support gives exactly finite vectors at the two endpoints. -/
theorem compact_project (I : List Nat) (f : Family) (live : Nat→Bool) (code back : Nat→Nat)
    (n : Nat) (hn : 1≤n) (hcode : code 1=1) (hback : back 1=1)
    (bounds : ∀ i, live i=true → 1≤code i ∧ code i≤n ∧ back (code i)=i)
    (supp : ∀ r∈I, supported live (f r)) (a : Rat) :
    project I f a ↔ RowsProject n (table I (fun i => renumber code (f i))) a := by
  constructor
  · rintro ⟨x,hx,hs⟩
    let y (i : Fin n) := x (back (i.val+1))
    have finite (i : Nat) (lo : 1≤i) (hi : i≤n) : finiteLift y i=x (back i) := by
      cases i with
      | zero => omega
      | succ i => simp [finiteLift,y,show i<n by omega]
    refine ⟨y,by rw [finite 1 (by decide) hn,hback,hx],(table_holds _ _ _).mpr ?_⟩
    intro r mem; rw [renumber_value]
    apply Eq.trans _ (hs r mem)
    apply supp r mem
    intro i hi; obtain ⟨lo,up,backi⟩ := bounds i hi
    rw [finite _ lo up,backi]
  · rintro ⟨y,hy,hs⟩
    refine ⟨fun i => finiteLift y (code i),by simpa [hcode] using hy,?_⟩
    intro r mem
    exact (renumber_value _ _ _).symm.trans ((table_holds _ _ _).mp hs r mem)

end ProjectionDescent
