import ComparisonChart
namespace PhysicalProjection.RootOrdinate
open PhysicalProjection.Comparison

/-- The single rational residual for the inverse of the first coefficient. -/
def equation (C : Q2) (u : Rat) := 2-2*C.1*u^2+C.2^2*u^4

def ordinate (C : Q2) (u : Rat) : Q2 := (C.1*u-C.2^2*u^3/2,C.2*u/2)

theorem emitted_form (C : Q2) (u : Rat) :
    equation C u=2*(1-u*(u*(C.1+(-1/2:Rat)*(C.2*u)^2))) := by unfold equation; grobner

/-- Squaring with prescribed inverse first coordinate is equivalent to one scalar residual. -/
theorem ordinate_iff (C y : Q2) (u : Rat) :
    (sq y=C ∧ u*y.1=1) ↔ equation C u=0 ∧ y=ordinate C u := by
  constructor
  · rintro ⟨rfl,unit⟩
    constructor
    · dsimp [equation,sq,times];grobner
    · apply Prod.ext <;> dsimp [ordinate,sq,times] <;> grobner
  · rintro ⟨eqn,rfl⟩
    unfold equation at eqn
    have unit : u*(ordinate C u).1=1 := by dsimp [ordinate];grobner
    refine ⟨?_,unit⟩
    apply Prod.ext <;> dsimp [sq,times,ordinate] <;> grobner

theorem ordinate_from_equation (C : Q2) (u : Rat) (h : equation C u=0) :
    sq (ordinate C u)=C ∧ u*(ordinate C u).1=1 :=
  (ordinate_iff C (ordinate C u) u).mpr ⟨h,rfl⟩

def sub (x y : Q2) : Q2 := (x.1-y.1,x.2-y.2)
def conjugate (a : Q2) : Q2 := (a.1,-a.2)
def fourth (a : Q2) := sq (sq a)
def root (a b : Q2) := sq b=sub (fourth a) D2
def Z (a : Q2) := sub ((norm a)^4,0) (times D2 (fourth (conjugate a)))
def M (a b : Q2) := times b (sq (conjugate a))
def recover (a m : Q2) : Q2 := let t:=times (sq a) m; (t.1/(norm a)^2,t.2/(norm a)^2)

private theorem square_nonneg (x : Rat) : 0≤x^2 := by
  rcases Rat.nonneg_total x with p|p
  · exact Rat.pow_nonneg p
  · have n:=Rat.mul_nonneg p p; rwa [show (-x)*(-x)=x^2 by grobner] at n

private theorem nz_pow {a : Rat} (n : Nat) (nonzero : a≠0) : a^n≠0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Rat.pow_succ]; intro z;exact (Rat.mul_eq_zero.mp z).elim ih nonzero

private theorem norm_ne {a : Q2} (ha : a≠(0,0)) : norm a≠0 := by
  intro zero
  obtain ⟨x,y⟩ := (CircuitTransport.Quadratic.norm_zero_iff a.1 a.2).mp zero
  exact ha (Prod.ext x y)

private theorem mul_assoc (a b c : Q2) : times (times a b) c=times a (times b c) := by
  apply Prod.ext <;> dsimp [times] <;> grobner

private theorem mul_comm (a b : Q2) : times a b=times b a := by
  apply Prod.ext <;> dsimp [times] <;> grobner

private theorem square_product (a b : Q2) : sq (times a b)=times (sq a) (sq b) := by
  apply Prod.ext <;> dsimp [sq,times] <;> grobner

private theorem times_sub (a b c : Q2) : times (sub a b) c=sub (times a c) (times b c) := by
  apply Prod.ext <;> dsimp [sub,times] <;> grobner

private theorem ab_squares (a : Q2) : times (sq a) (sq (conjugate a))=((norm a)^2,0) := by
  apply Prod.ext <;> dsimp [conjugate,times,sq,norm] <;> grobner

private theorem fourth_product (a : Q2) : times (fourth a) (fourth (conjugate a))=((norm a)^4,0) := by
  unfold fourth; rw [←square_product,ab_squares]; apply Prod.ext <;> dsimp [sq,times] <;> grobner

private theorem zero_cancel {x y : Q2} (ny : norm y≠0) (zero : times x y=(0,0)) : x=(0,0) := by
  have z : norm x*norm y=0 := by rw [←norm_product,zero];unfold norm;grobner
  have n: norm x=0 := (Rat.mul_eq_zero.mp z).resolve_right ny
  obtain ⟨a,b⟩ := (CircuitTransport.Quadratic.norm_zero_iff x.1 x.2).mp n
  exact Prod.ext a b

private theorem cancel_right {x y z : Q2} (nz : norm z≠0) (eq : times x z=times y z) : x=y := by
  have zero : sub x y=(0,0) := zero_cancel nz (by rw [times_sub,eq];apply Prod.ext <;> dsimp [sub] <;> grobner)
  have a:=congrArg Prod.fst zero;have b:=congrArg Prod.snd zero
  apply Prod.ext <;> dsimp [sub] at a b <;> grobner

/-- The original root equation already excludes the zero abscissa parameter. -/
theorem root_nonzero {a b : Q2} (rt : root a b) : a≠(0,0) := by
  intro zero;subst a
  have re:=congrArg Prod.fst rt
  have p:=square_nonneg b.1;have q:=square_nonneg b.2
  have eq : b.1^2+2*b.2^2= -11 := by dsimp [sq,sub,fourth,times,D2] at re;grobner
  grind

/-- Outside `a=0`, squaring the transported ordinate is equivalent to the original field equation. -/
theorem root_transport (a b : Q2) (ha : a≠(0,0)) : root a b ↔ sq (M a b)=Z a := by
  have den : norm (fourth (conjugate a))≠0 := by
    have id : norm (fourth (conjugate a))=(norm a)^4 := by
      unfold fourth sq;rw [norm_product,norm_product];dsimp [norm,conjugate];grobner
    rw [id]; exact nz_pow 4 (norm_ne ha)
  have transform : times (sub (fourth a) D2) (fourth (conjugate a))=Z a := by
    rw [times_sub,fourth_product];rfl
  change sq b=sub (fourth a) D2 ↔ sq (times b (sq (conjugate a)))=Z a
  rw [square_product,←transform]
  exact ⟨fun eq => by rw [eq];rfl, fun eq => cancel_right den eq⟩

/-- The scalar equation itself excludes `a=0`, before any division by its norm. -/
theorem scalar_nonzero {a : Q2} {u : Rat} (h : equation (Z a) u=0) : a≠(0,0) := by
  intro z;subst a;dsimp [equation,Z,norm,sub,times,D2,conjugate,fourth,sq] at h;grobner

/-- Multiplying by `a²/N(a)²` is the inverse of multiplication by the conjugate square. -/
theorem recover_inverse (a m : Q2) (ha : a≠(0,0)) : M a (recover a m)=m := by
  let n:=(norm a)^2
  let p:=times (sq a) m
  have nz : n≠0 := nz_pow 2 (norm_ne ha)
  have x : (recover a m).1*n=p.1 := Rat.div_mul_cancel nz
  have y : (recover a m).2*n=p.2 := Rat.div_mul_cancel nz
  have scaled : times (recover a m) (n,0)=p := by apply Prod.ext <;> dsimp [times] <;> grobner
  have same : times (M a (recover a m)) (n,0)=times m (n,0) := by
    calc times (M a (recover a m)) (n,0) = times (times (recover a m) (n,0)) (sq (conjugate a)) := by
           unfold M;rw [mul_assoc,mul_comm (sq (conjugate a)),←mul_assoc]
         _ = times (times m (sq a)) (sq (conjugate a)) := by rw [scaled];change times (times (sq a) m) _=_;rw [mul_comm (sq a) m]
         _ = times m (n,0) := by rw [mul_assoc,ab_squares]
  apply cancel_right _ same
  change n^2-2*(0:Rat)^2≠0
  rw [show n^2-2*(0:Rat)^2=n^2 by grobner];exact nz_pow 2 nz

/-- The inverse also recovers the chosen sign of an original root. -/
theorem recover_of_M (a b : Q2) (ha : a≠(0,0)) : recover a (M a b)=b := by
  have exactNorm : norm (sq (conjugate a))=(norm a)^2 := by
    unfold sq;rw [norm_product];dsimp [norm,conjugate];grobner
  have n : norm (sq (conjugate a))≠0 := exactNorm ▸ nz_pow 2 (norm_ne ha)
  exact cancel_right n (recover_inverse a (M a b) ha)

/-- The comparison obstruction applies to the conjugate fourth-power term in `Z`. -/
theorem transported_real_nonzero {a b : Q2} (rt : root a b) : (M a b).1≠0 := by
  have nz:=root_nonzero rt
  have nc : conjugate a≠(0,0) := by
    intro zero;apply nz
    have x:=congrArg Prod.fst zero;have y:=congrArg Prod.snd zero
    apply Prod.ext <;> dsimp [conjugate] at x y <;> grobner
  have f:=fourth_imaginary_nonzero nc
  have im:=congrArg Prod.snd ((root_transport a b nz).mp rt)
  intro zero
  change (M a b).1*(M a b).2+(M a b).2*(M a b).1=0-(times D2 (fourth (conjugate a))).2 at im
  rw [zero] at im
  exact f (by change (times D2 (fourth (conjugate a))).2=0;grobner)

/-- The encoded scalar lifts to the displayed ordinate `b=a²M/N(a)²`. -/
theorem decoded_root {a : Q2} {u : Rat} (h : equation (Z a) u=0) :
    let m:=ordinate (Z a) u; let b:=recover a m
    root a b ∧ M a b=m ∧ u*(M a b).1=1 := by
  let m:=ordinate (Z a) u;let b:=recover a m
  have nz:=scalar_nonzero h
  have undo : M a b=m := recover_inverse a m nz
  obtain ⟨square,unit⟩:=ordinate_from_equation _ _ h
  exact ⟨(root_transport a b nz).mpr (undo ▸ square),undo,undo ▸ unit⟩

/-- Exact correspondence for a specified root, including its sign. -/
theorem root_pointwise (a b : Q2) (u : Rat) :
    (root a b ∧ u*(M a b).1=1) ↔ equation (Z a) u=0 ∧ b=recover a (ordinate (Z a) u) := by
  constructor
  · rintro ⟨rt,unit⟩
    have nz:=root_nonzero rt
    obtain ⟨h,which⟩ := (ordinate_iff (Z a) (M a b) u).mp ⟨(root_transport a b nz).mp rt,unit⟩
    exact ⟨h,by rw [←which,recover_of_M a b nz]⟩
  · rintro ⟨h,rfl⟩;have lift:=decoded_root h;exact ⟨lift.1,lift.2.2⟩

theorem root_equivalence (a : Q2) : (∃ b : Q2, root a b) ↔ ∃ u : Rat, equation (Z a) u=0 := by
  constructor
  · rintro ⟨b,rt⟩
    let m:=M a b
    have nz : m.1≠0:=transported_real_nonzero rt
    exact ⟨m.1⁻¹,((ordinate_iff (Z a) m m.1⁻¹).mp ⟨(root_transport a b (root_nonzero rt)).mp rt,Rat.inv_mul_cancel _ nz⟩).1⟩
  · rintro ⟨u,h⟩;exact ⟨recover a (ordinate (Z a) u),(decoded_root h).1⟩

def target (r : Q2) := sub one (times D2 (fourth r))

private theorem conic_square (r J : Q2) : conic r J ↔ sq J=target r := by
  constructor <;> intro h <;> have a:=congrArg Prod.fst h <;> have b:=congrArg Prod.snd h
  · apply Prod.ext <;> dsimp only [conic,target,sub,one,fourth] at a b ⊢ <;> grobner
  · apply Prod.ext <;> dsimp only [conic,target,sub,one,fourth] at a b ⊢ <;> grobner

theorem comparison_equivalence (r : Q2) : (∃ J : Q2, conic r J) ↔ ∃ v : Rat, equation (target r) v=0 := by
  constructor
  · rintro ⟨J,h⟩
    exact ⟨J.1⁻¹,((ordinate_iff (target r) J J.1⁻¹).mp ⟨(conic_square r J).mp h,Rat.inv_mul_cancel _ (ordinate_real_nonzero h)⟩).1⟩
  · rintro ⟨v,h⟩;exact ⟨ordinate (target r) v,(conic_square ..).mpr (ordinate_from_equation _ _ h).1⟩

theorem comparison_pointwise (r J : Q2) (v : Rat) :
    (conic r J ∧ v*J.1=1) ↔ equation (target r) v=0 ∧ J=ordinate (target r) v := by
  rw [conic_square];exact ordinate_iff _ _ _

/-- At fixed eight old ordinates the explicit inverse gives the same eight values. -/
theorem eight_points (a b r J : Fin 4→Q2) :
    (∀ i, root (a i) (b i) ∧ conic (r i) (J i)) ↔ ∃ u v : Fin 4→Rat, ∀ i,
      (equation (Z (a i)) (u i)=0 ∧ b i=recover (a i) (ordinate (Z (a i)) (u i))) ∧
      (equation (target (r i)) (v i)=0 ∧ J i=ordinate (target (r i)) (v i)) := by
  constructor
  · intro h
    refine ⟨fun i=>(M (a i) (b i)).1⁻¹,fun i=>(J i).1⁻¹,?_⟩
    intro i
    exact ⟨(root_pointwise ..).mp ⟨(h i).1,Rat.inv_mul_cancel _ (transported_real_nonzero (h i).1)⟩,
           (comparison_pointwise ..).mp ⟨(h i).2,Rat.inv_mul_cancel _ (ordinate_real_nonzero (h i).2)⟩⟩
  · rintro ⟨u,v,h⟩ i
    exact ⟨((root_pointwise (a i) (b i) (u i)).mpr (h i).1).1,
           ((comparison_pointwise (r i) (J i) (v i)).mpr (h i).2).1⟩

/-- Four field root ordinates and four comparison ordinates have eight scalar rational witnesses. -/
theorem eight_ordinates (a r : Fin 4→Q2) :
    (∀ i, (∃ b : Q2, root (a i) b) ∧ ∃ J : Q2, conic (r i) J) ↔
    ∃ u v : Fin 4→Rat, ∀ i, equation (Z (a i)) (u i)=0 ∧ equation (target (r i)) (v i)=0 := by
  constructor
  · intro h
    have roots (i) := (root_equivalence (a i)).mp (h i).1
    have comps (i) := (comparison_equivalence (r i)).mp (h i).2
    exact ⟨fun i=>Classical.choose (roots i),fun i=>Classical.choose (comps i),fun i=>⟨Classical.choose_spec (roots i),Classical.choose_spec (comps i)⟩⟩
  · rintro ⟨u,v,h⟩ i
    exact ⟨(root_equivalence (a i)).mpr ⟨u i,(h i).1⟩,(comparison_equivalence (r i)).mpr ⟨v i,(h i).2⟩⟩

#print axioms emitted_form
#print axioms ordinate_iff
#print axioms ordinate_from_equation
#print axioms root_nonzero
#print axioms root_transport
#print axioms scalar_nonzero
#print axioms recover_inverse
#print axioms recover_of_M
#print axioms transported_real_nonzero
#print axioms decoded_root
#print axioms root_pointwise
#print axioms root_equivalence
#print axioms comparison_equivalence
#print axioms comparison_pointwise
#print axioms eight_points
#print axioms eight_ordinates
end PhysicalProjection.RootOrdinate
