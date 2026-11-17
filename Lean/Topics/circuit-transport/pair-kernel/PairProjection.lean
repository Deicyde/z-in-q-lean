import Std

namespace CircuitTransport.Pair

/-- The two rational values have (possibly zero) rational square roots. -/
def Roots (a b : Rat) : Prop := ∃ x y : Rat, x^2=a ∧ y^2=b

def quartic (a b z : Rat) : Rat := 1-2*(a+b)*z^2+((a-b)*z^2)^2

def ordinary (a b u : Rat) : Rat := (a^2+b^2)*quartic a b u

def guarded (a b h u : Rat) : Rat := (a^2+b^2+(h*u-1)^2)*quartic a b (h*u)

private theorem nonzeroMul {a b : Rat} (ha : a≠0) (hb : b≠0) : a*b≠0 := by
  intro h; exact (Rat.mul_eq_zero.mp h).elim ha hb

private theorem sq_eq_zero {r : Rat} (h : r^2=0) : r=0 := by
  have v : r*r=0 := by grobner
  exact (Rat.mul_eq_zero.mp v).elim id id

private theorem sq_nonneg (r : Rat) : 0≤r^2 := by
  rcases Rat.nonneg_total r with h|h
  · exact Rat.pow_nonneg h
  · have n := Rat.mul_nonneg h h
    rwa [show -r*(-r)=r^2 by grobner] at n

private theorem sum_zero {a b : Rat} (ha : 0≤a) (hb : 0≤b) (h : a+b=0) : a=0 ∧ b=0 := by
  grind

private theorem two_zero {a b : Rat} (zero : a^2+b^2=0) : a=0 ∧ b=0 := by
  obtain ⟨s,t⟩ := sum_zero (sq_nonneg a) (sq_nonneg b) zero
  exact ⟨sq_eq_zero s,sq_eq_zero t⟩

private theorem cancel {r x y : Rat} (hr : r≠0) (h : x*r=y*r) : x=y := by grind

private theorem quartic_ne_zero {a b z : Rat} (point : quartic a b z=0) : z≠0 := by
  intro equal
  subst z
  unfold quartic at point
  grobner

/-- Given the reciprocal-sum parameter, recover the two square roots themselves. -/
theorem quartic_roots {a b z : Rat} (point : quartic a b z=0) : Roots a b := by
  have hz := quartic_ne_zero point
  let d := 2*z
  have hd : d≠0 := nonzeroMul (by decide) hz
  let x := (1+(a-b)*z^2)/d
  let y := (1-(a-b)*z^2)/d
  have px : x*d=1+(a-b)*z^2 := Rat.div_mul_cancel hd
  have py : y*d=1-(a-b)*z^2 := Rat.div_mul_cancel hd
  have sd : d^2≠0 := fun h => hd (sq_eq_zero h)
  unfold quartic at point
  refine ⟨x,y,?_,?_⟩
  · apply cancel sd
    calc x^2*d^2 = (x*d)^2 := by grobner
         _ = a*d^2 := by rw [px]; dsimp [d]; grobner
  · apply cancel sd
    calc y^2*d^2 = (y*d)^2 := by grobner
         _ = b*d^2 := by rw [py]; dsimp [d]; grobner

private theorem reciprocal {x y : Rat} (hxy : x+y≠0) : ∃ z : Rat, quartic (x^2) (y^2) z=0 := by
  let z := (x+y)⁻¹
  have recip : (x+y)*z=1 := Rat.mul_inv_cancel _ hxy
  refine ⟨z,?_⟩
  calc quartic (x^2) (y^2) z = (1-((x+y)*z)^2)*(1-((x-y)*z)^2) := by unfold quartic; grobner
       _ = 0 := by rw [recip]; grobner

/-- The bare quartic also excludes the double zero. -/
theorem quartic_iff (a b : Rat) :
    (∃ z : Rat, quartic a b z=0) ↔ Roots a b ∧ ¬(a=0 ∧ b=0) := by
  constructor
  · rintro ⟨z,good⟩
    refine ⟨quartic_roots good,?_⟩
    rintro ⟨rfl,rfl⟩
    unfold quartic at good; grobner
  · rintro ⟨⟨x,y,rfl,rfl⟩,nontrivial⟩
    by_cases h : x+y=0
    · have other : x+(-y)≠0 := by
        intro bad
        apply nontrivial
        exact ⟨by grobner,by grobner⟩
      obtain ⟨z,q⟩ := reciprocal other
      exact ⟨z,by rw [show (-y)^2=y^2 by grobner] at q; exact q⟩
    · exact reciprocal h

/-- The literal product with `a²+b²` restores the double zero. -/
theorem ordinary_iff (a b : Rat) : (∃ u : Rat, ordinary a b u=0) ↔ Roots a b := by
  constructor
  · rintro ⟨u,point⟩
    rcases Rat.mul_eq_zero.mp point with zero|quart
    · obtain ⟨rfl,rfl⟩ := two_zero zero
      exact ⟨0,0,by decide,by decide⟩
    · exact quartic_roots quart
  · intro roots
    by_cases z : a=0 ∧ b=0
    · obtain ⟨rfl,rfl⟩ := z
      exact ⟨0,by unfold ordinary; grobner⟩
    · obtain ⟨u,q⟩ := (quartic_iff a b).mpr ⟨roots,z⟩
      exact ⟨u,by unfold ordinary; rw [q]; grobner⟩

/-- The guarded polynomial enforces nonzero `h`, including at `(a,b)=(0,0)`. -/
theorem guarded_iff (a b h : Rat) : (∃ u : Rat, guarded a b h u=0) ↔ h≠0 ∧ Roots a b := by
  constructor
  · rintro ⟨u,point⟩
    rcases Rat.mul_eq_zero.mp point with zero|quart
    · have nab := Rat.add_nonneg (sq_nonneg a) (sq_nonneg b)
      obtain ⟨zeros,unit⟩ := sum_zero nab (sq_nonneg (h*u-1)) zero
      obtain ⟨rfl,rfl⟩ := two_zero zeros
      refine ⟨?_,⟨0,0,by decide,by decide⟩⟩
      intro hz; rw [hz] at unit; grobner
    · refine ⟨?_,quartic_roots quart⟩
      intro z
      exact quartic_ne_zero quart (by rw [z,Rat.zero_mul])
  · rintro ⟨hh,roots⟩
    by_cases zero : a=0 ∧ b=0
    · obtain ⟨rfl,rfl⟩ := zero
      refine ⟨h⁻¹,?_⟩
      unfold guarded; rw [Rat.mul_inv_cancel _ hh]; grobner
    · obtain ⟨z,q⟩ := (quartic_iff a b).mpr ⟨roots,zero⟩
      have hz : h*(z/h)=z := by rw [Rat.mul_comm,Rat.div_mul_cancel hh]
      refine ⟨z/h,?_⟩
      unfold guarded; rw [hz,q]; grobner

/-- Two affine equations `ax+by=r, cx+dy=s`. -/
structure Block where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  r : Rat
  s : Rat

def Block.det (B : Block) : Rat := B.a*B.d-B.b*B.c

def Block.xAdj (B : Block) : Rat := B.r*B.d-B.b*B.s

def Block.yAdj (B : Block) : Rat := B.a*B.s-B.r*B.c

def Block.holds (B : Block) (x y : Rat) : Prop := B.a*x+B.b*y=B.r ∧ B.c*x+B.d*y=B.s

def Block.scaled (B : Block) (h x y : Rat) : Prop := B.a*x+B.b*y=h*B.r ∧ B.c*x+B.d*y=h*B.s

def Block.zeroMatrix (B : Block) : Prop := B.a=0 ∧ B.b=0 ∧ B.c=0 ∧ B.d=0

def Block.zeroSystem (B : Block) : Prop := B.zeroMatrix ∧ B.r=0 ∧ B.s=0

def total (f : Block → Rat) : List Block → Rat
  | [] => 0
  | b::bs => f b + total f bs

def H (bs : List Block) := total (fun b => b.det^2) bs

def Nx (bs : List Block) := total (fun b => b.det*b.xAdj) bs

def Ny (bs : List Block) := total (fun b => b.det*b.yAdj) bs

private theorem hNonnegative (bs : List Block) : 0≤H bs := by
  induction bs with
  | nil => decide
  | cons b bs ih => exact Rat.add_nonneg (sq_nonneg b.det) ih

private theorem det_zero_of_h_zero {bs : List Block} (hz : H bs=0) : ∀ b∈bs, b.det=0 := by
  induction bs with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨hc,hs⟩ := sum_zero (sq_nonneg c.det) (hNonnegative cs) hz
    intro b hb
    rcases List.mem_cons.mp hb with atHead|later
    · exact atHead ▸ sq_eq_zero hc
    · exact ih hs b later

private theorem adj_at_solution {b : Block} {x y : Rat} (point : b.holds x y) :
    b.xAdj=b.det*x ∧ b.yAdj=b.det*y := by
  obtain ⟨first,second⟩ := point
  unfold Block.xAdj Block.yAdj Block.det
  rw [←first,←second]
  exact ⟨by grobner,by grobner⟩

/-- Weighted adjugates give the same numerator for every rational solution. -/
theorem numerators {bs : List Block} {x y : Rat} (sol : ∀ b∈bs, b.holds x y) :
    Nx bs=H bs*x ∧ Ny bs=H bs*y := by
  induction bs with
  | nil => exact ⟨by unfold Nx H total; grobner,by unfold Ny H total; grobner⟩
  | cons b bs ih =>
    obtain ⟨headX,headY⟩ := adj_at_solution (sol b (by simp))
    obtain ⟨tailX,tailY⟩ := ih (fun c hc => sol c (List.mem_cons_of_mem _ hc))
    change b.det*b.xAdj + Nx bs = (b.det^2 + H bs)*x ∧
      b.det*b.yAdj + Ny bs = (b.det^2 + H bs)*y
    rw [headX,headY,tailX,tailY]
    exact ⟨by grobner,by grobner⟩

/-- Every singular coefficient block is required to be the zero matrix. -/
def NoRankOne (bs : List Block) := ∀ b∈bs, b.det=0 → b.zeroMatrix

def Consistent (bs : List Block) := ∃ x y : Rat, ∀ b∈bs, b.holds x y

def RegularRows (bs : List Block) := ∀ b∈bs, b.scaled (H bs) (Nx bs) (Ny bs)

def ZeroRows (bs : List Block) := ∀ b∈bs, b.zeroSystem

/-- Exact finite paired-row projection, including an empty list and zero matrices. -/
theorem adjugate_iff {bs : List Block} (shapes : NoRankOne bs) :
    Consistent bs ↔ ((H bs≠0 ∧ RegularRows bs) ∨ ZeroRows bs) := by
  constructor
  · rintro ⟨x,y,sol⟩
    by_cases hz : H bs=0
    · right
      intro b hb
      have matrix := shapes b hb (det_zero_of_h_zero hz b hb)
      obtain ⟨a0,b0,c0,d0⟩ := matrix
      obtain ⟨r,s⟩ := sol b hb
      exact ⟨⟨a0,b0,c0,d0⟩,by rw [←r,a0,b0]; grobner,by rw [←s,c0,d0]; grobner⟩
    · left
      refine ⟨hz,?_⟩
      obtain ⟨nx,ny⟩ := numerators sol
      intro b hb
      obtain ⟨r,s⟩ := sol b hb
      unfold Block.scaled
      rw [nx,ny,←r,←s]
      exact ⟨by grobner,by grobner⟩
  · rintro (⟨hz,scaled⟩|zero)
    · let x := Nx bs/H bs
      let y := Ny bs/H bs
      have nx : x*H bs=Nx bs := Rat.div_mul_cancel hz
      have ny : y*H bs=Ny bs := Rat.div_mul_cancel hz
      refine ⟨x,y,?_⟩
      intro b hb
      obtain ⟨r,s⟩ := scaled b hb
      constructor
      · apply cancel hz
        calc (b.a*x+b.b*y)*H bs = b.a*(x*H bs)+b.b*(y*H bs) := by grobner
             _ = b.r*H bs := by rw [nx,ny,r]; grobner
      · apply cancel hz
        calc (b.c*x+b.d*y)*H bs = b.c*(x*H bs)+b.d*(y*H bs) := by grobner
             _ = b.s*H bs := by rw [nx,ny,s]; grobner
    · refine ⟨0,0,?_⟩
      intro b hb
      obtain ⟨_,r,s⟩ := zero b hb
      exact ⟨by rw [r]; grobner,by rw [s]; grobner⟩

/-- The choice of two parameters enforces four rational squares and the linear system. -/
theorem paired_projection {bs : List Block} (shapes : NoRankOne bs) (a b c d : Rat) :
    (Consistent bs ∧ Roots a b ∧ Roots c d) ↔
      ∃ u v : Rat, ((RegularRows bs ∧ guarded a b (H bs) u=0) ∨
                    (ZeroRows bs ∧ ordinary a b u=0)) ∧ ordinary c d v=0 := by
  constructor
  · rintro ⟨sol,first,second⟩
    obtain ⟨v,sv⟩ := (ordinary_iff c d).mpr second
    rcases (adjugate_iff shapes).mp sol with ⟨hz,rows⟩|rows
    · obtain ⟨u,gu⟩ := (guarded_iff a b (H bs)).mpr ⟨hz,first⟩
      exact ⟨u,v,Or.inl ⟨rows,gu⟩,sv⟩
    · obtain ⟨u,ou⟩ := (ordinary_iff a b).mpr first
      exact ⟨u,v,Or.inr ⟨rows,ou⟩,sv⟩
  · rintro ⟨u,v,options,sv⟩
    have second := (ordinary_iff c d).mp ⟨v,sv⟩
    rcases options with ⟨rows,gu⟩|⟨rows,ou⟩
    · obtain ⟨hz,first⟩ := (guarded_iff a b (H bs)).mp ⟨u,gu⟩
      exact ⟨(adjugate_iff shapes).mpr (Or.inl ⟨hz,rows⟩),first,second⟩
    · exact ⟨(adjugate_iff shapes).mpr (Or.inr rows),(ordinary_iff a b).mp ⟨u,ou⟩,second⟩

private def squares : List Rat → Rat
  | [] => 0
  | x::xs => x^2 + squares xs

private theorem squares_nonneg (xs : List Rat) : 0≤squares xs := by
  induction xs with
  | nil => decide
  | cons x xs ih => exact Rat.add_nonneg (sq_nonneg x) ih

private theorem squares_zero (xs : List Rat) : squares xs=0 ↔ ∀ x∈xs, x=0 := by
  induction xs with
  | nil => simp [squares]
  | cons x xs ih =>
    constructor
    · intro all r hr
      obtain ⟨head,tail⟩ := sum_zero (sq_nonneg x) (squares_nonneg xs) all
      rcases List.mem_cons.mp hr with first|later
      · exact first ▸ sq_eq_zero head
      · exact ih.mp tail r later
    · intro all
      have head := all x (by simp)
      have tail := ih.mpr (fun z hz => all z (List.mem_cons_of_mem _ hz))
      change x^2+squares xs=0
      rw [head,tail]; grobner

private theorem total_nonneg (f : Block → Rat) (hf : ∀ B, 0≤f B) (bs : List Block) : 0≤total f bs := by
  induction bs with
  | nil => change (0:Rat)≤0; decide
  | cons B bs ih => exact Rat.add_nonneg (hf B) ih

private theorem total_zero (f : Block → Rat) (hf : ∀ B, 0≤f B) (bs : List Block) :
    total f bs=0 ↔ ∀ B∈bs, f B=0 := by
  induction bs with
  | nil => simp [total]
  | cons B bs ih =>
    constructor
    · intro all r hr
      obtain ⟨head,tail⟩ := sum_zero (hf B) (total_nonneg f hf bs) all
      rcases List.mem_cons.mp hr with first|later
      · exact first ▸ head
      · exact ih.mp tail r later
    · intro all
      have head := all B (by simp)
      have tail := ih.mpr (fun z hz => all z (List.mem_cons_of_mem _ hz))
      change f B+total f bs=0
      rw [head,tail]; grobner

private def Block.regularValue (h x y : Rat) (B : Block) :=
  squares [B.a*x+B.b*y-h*B.r,B.c*x+B.d*y-h*B.s]

private def Block.zeroValue (B : Block) := squares [B.a,B.b,B.c,B.d,B.r,B.s]

private theorem regular_value (h x y : Rat) (B : Block) : B.regularValue h x y=0 ↔ B.scaled h x y := by
  change squares _=0 ↔ _
  have pair (A Z : Rat) : (∀ r∈[A,Z], r=0) ↔ A=0 ∧ Z=0 := by simp
  rw [squares_zero,pair]
  constructor <;> rintro ⟨first,second⟩ <;> exact ⟨by grobner,by grobner⟩

private theorem zero_value (B : Block) : B.zeroValue=0 ↔ B.zeroSystem := by
  change squares _=0 ↔ _
  rw [squares_zero]; simp [Block.zeroSystem,Block.zeroMatrix,and_assoc]

private def regularLoss (bs : List Block) (a b u : Rat) :=
  total (Block.regularValue (H bs) (Nx bs) (Ny bs)) bs + (guarded a b (H bs) u)^2

private def zeroLoss (bs : List Block) (a b u : Rat) :=
  total Block.zeroValue bs + (ordinary a b u)^2

/-- The two-block summand of the literal polynomial, up to addition associativity. -/
def pairValue (bs : List Block) (a b c d u v : Rat) :=
  regularLoss bs a b u * zeroLoss bs a b u + (ordinary c d v)^2

private theorem reg_nonneg (bs : List Block) (a b u : Rat) : 0≤regularLoss bs a b u :=
  Rat.add_nonneg (total_nonneg _ (fun _ => squares_nonneg _) _) (sq_nonneg _)

private theorem zero_nonneg (bs : List Block) (a b u : Rat) : 0≤zeroLoss bs a b u :=
  Rat.add_nonneg (total_nonneg _ (fun _ => squares_nonneg _) _) (sq_nonneg _)

/-- The branch product can be added directly to the remaining squares. -/
theorem pairValue_nonnegative (bs : List Block) (a b c d u v : Rat) : 0≤pairValue bs a b c d u v :=
  Rat.add_nonneg (Rat.mul_nonneg (reg_nonneg ..) (zero_nonneg ..)) (sq_nonneg _)

private theorem total_sq (f : Block → Rat) (hf : ∀ B, 0≤f B) (bs : List Block) (z : Rat) :
    total f bs+z^2=0 ↔ (∀ B∈bs, f B=0) ∧ z=0 := by
  constructor
  · intro h
    obtain ⟨left,right⟩ := sum_zero (total_nonneg f hf bs) (sq_nonneg z) h
    exact ⟨(total_zero f hf bs).mp left,sq_eq_zero right⟩
  · rintro ⟨left,rfl⟩
    rw [(total_zero f hf bs).mpr left]; grobner

private theorem regular_loss (bs : List Block) (a b u : Rat) :
    regularLoss bs a b u=0 ↔ RegularRows bs ∧ guarded a b (H bs) u=0 := by
  unfold regularLoss RegularRows
  rw [total_sq (Block.regularValue (H bs) (Nx bs) (Ny bs)) (fun _ => squares_nonneg _) bs _]
  simp only [regular_value]

private theorem zero_loss (bs : List Block) (a b u : Rat) :
    zeroLoss bs a b u=0 ↔ ZeroRows bs ∧ ordinary a b u=0 := by
  unfold zeroLoss ZeroRows
  rw [total_sq Block.zeroValue (fun _ => squares_nonneg _) bs _]
  simp only [zero_value]

private theorem pair_at (bs : List Block) (a b c d u v : Rat) :
    pairValue bs a b c d u v=0 ↔
    ((RegularRows bs ∧ guarded a b (H bs) u=0) ∨ (ZeroRows bs ∧ ordinary a b u=0)) ∧ ordinary c d v=0 := by
  constructor
  · intro h
    obtain ⟨mult,square⟩ := sum_zero (Rat.mul_nonneg (reg_nonneg ..) (zero_nonneg ..)) (sq_nonneg _) h
    refine ⟨?_,sq_eq_zero square⟩
    exact (Rat.mul_eq_zero.mp mult).imp (regular_loss bs a b u).mp (zero_loss bs a b u).mp
  · rintro ⟨branches,other⟩
    have mult := Rat.mul_eq_zero.mpr (branches.imp (regular_loss bs a b u).mpr (zero_loss bs a b u).mpr)
    unfold pairValue; rw [mult,other]; grobner

/-- Exact finite-list polynomial characterization with only two auxiliary parameters. -/
theorem pairValue_iff {bs : List Block} (shapes : NoRankOne bs) (a b c d : Rat) :
    (∃ u v : Rat, pairValue bs a b c d u v=0) ↔ Consistent bs ∧ Roots a b ∧ Roots c d := by
  rw [paired_projection shapes]
  simp only [pair_at]

#print axioms quartic_roots
#print axioms quartic_iff
#print axioms ordinary_iff
#print axioms guarded_iff
#print axioms numerators
#print axioms adjugate_iff
#print axioms paired_projection
#print axioms pairValue_nonnegative
#print axioms pairValue_iff

end CircuitTransport.Pair
