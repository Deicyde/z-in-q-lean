import GuardedTower
import RationalWitness

/-! Simultaneous signed ordinates on the nine affine abscissae. -/
open ZInQBlueprint.SunResultant
namespace Sun28.Concrete
open Sun28.Ordinates Sun28.RootCharts Sun28.WitnessIndices
noncomputable section
variable {R : Type*} [CommRing R] {n : ℕ}

def curveTest (u v : R) (y : K) (φ : R →+* ℚ) : Prop :=
  y^2 = (pair (φ u) (φ v))^3 - pair 11 (-6) * pair (φ u) (φ v)

private theorem curve_step (r : Row R n) (φ : R →+* ℚ) (x : Fin n → ℚ) (u v : R) (y : K) :
    (r.Holds φ x ∧ curveTest u v y φ) ↔
      ∃ (k : Branch) (w : ℚ),
        (r.signed k (MvPolynomial.C (realNumerator u v))
          (MvPolynomial.C (radicalNumerator u v)) 1).Holds φ (Fin.cons w x) ∧
        reads φ (Fin.cons w x) (signedOutput k (MvPolynomial.C (radicalNumerator u v)) 1) y := by
  simpa [curveTest,curve_rhs,realNumerator,radicalNumerator,ordinateReal,ordinateRadical,ev,map_ofNat] using
    signed_square r φ x (MvPolynomial.C (realNumerator u v)) (MvPolynomial.C (radicalNumerator u v)) 1 y

def sheet : {n : ℕ} → (Fin n → Branch) → (Fin n → R) → (Fin n → R) → Row R n
  | 0, _,_,_ => Row.base
  | n+1,k,u,v => (sheet (n:=n) (Fin.tail k) (Fin.tail u) (Fin.tail v)).signed (k 0)
      (MvPolynomial.C (realNumerator (u 0) (v 0))) (MvPolynomial.C (radicalNumerator (u 0) (v 0))) 1

abbrev Triple (R : Type*) := R × R × R

def liftOutput (q : Triple (Test R n)) : Triple (Test R (n+1)) :=
  (liftTest q.1,liftTest q.2.1,liftTest q.2.2)

theorem reads_lift (φ : R →+* ℚ) (x : Fin n → ℚ) (w : ℚ) (q : Triple (Test R n)) (y : K) :
    reads φ (Fin.cons w x) (liftOutput q) y ↔ reads φ x q y := by
  simp only [reads,liftOutput,eval_lift]

def ordinateOutputs : {n : ℕ} → (Fin n → Branch) → (Fin n → R) → (Fin n → R) →
    Fin n → Triple (Test R n)
  | 0,_,_,_ => Fin.elim0
  | n+1,k,u,v => Fin.cons
      (signedOutput (k 0) (MvPolynomial.C (radicalNumerator (u 0) (v 0))) 1)
      (fun i => liftOutput (ordinateOutputs (n:=n) (Fin.tail k) (Fin.tail u) (Fin.tail v) i))

theorem sheet_spec (φ : R →+* ℚ) (u v : Fin n → R) (y : Fin n → K) :
    (∀ i, curveTest (u i) (v i) (y i) φ) ↔
      ∃ (k : Fin n → Branch) (x : Fin n → ℚ), (sheet k u v).Holds φ x ∧
        ∀ i, reads φ x (ordinateOutputs k u v i) (y i) := by
  induction n with
  | zero =>
    exact ⟨fun _ => ⟨Fin.elim0,Fin.elim0,by simp [sheet,Row.base,Row.Holds,ParamTower.Satisfies],
      fun i => i.elim0⟩,fun _ i => i.elim0⟩
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨k,x,hx,hy⟩ := (ih (Fin.tail u) (Fin.tail v) (Fin.tail y)).1 (fun i => h i.succ)
      obtain ⟨b,w,hs,hw⟩ := (curve_step _ _ _ _ _ _).1 ⟨hx,h 0⟩
      refine ⟨Fin.cons b k,Fin.cons w x,?_,?_⟩
      · simpa only [sheet,Fin.tail_cons,Fin.cons_zero] using hs
      · refine Fin.cases ?_ (fun i => ?_)
        · simpa only [ordinateOutputs,Fin.cons_zero] using hw
        · simpa only [ordinateOutputs,Fin.cons_succ,Fin.tail_cons,reads_lift,Fin.tail] using hy i
    · rintro ⟨k,x,hr,hy⟩
      let z := Fin.tail x
      have hx : Fin.cons (x 0) z = x := Fin.cons_self_tail x
      let prev := sheet (Fin.tail k) (Fin.tail u) (Fin.tail v)
      have step := (curve_step prev φ z (u 0) (v 0) (y 0)).2
        ⟨k 0,x 0,by simpa only [hx,sheet,prev] using hr,
          by simpa only [hx,ordinateOutputs,Fin.cons_zero] using hy 0⟩
      have lt (i : Fin n) : reads φ z
          (ordinateOutputs (Fin.tail k) (Fin.tail u) (Fin.tail v) i) (Fin.tail y i) := by
        apply (reads_lift φ z (x 0) _ _).1
        rw [hx]
        simpa only [ordinateOutputs,Fin.cons_succ,Fin.tail] using hy i.succ
      exact Fin.cases step.2 ((ih (Fin.tail u) (Fin.tail v) (Fin.tail y)).2 ⟨Fin.tail k,z,step.1,lt⟩)

def patterns : (n : ℕ) → List (Fin n → Branch)
  | 0 => [Fin.elim0]
  | n+1 => [Branch.mixed,.realPart,.radicalPart,.zero].flatMap fun b =>
      (patterns n).map (Fin.cons b)

theorem mem_patterns (k : Fin n → Branch) : k ∈ patterns n := by
  induction n with
  | zero =>
    have h : k = Fin.elim0 := Subsingleton.elim _ _
    simp [patterns,h]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨k 0,?_,List.mem_map.mpr ⟨Fin.tail k,ih _,Fin.cons_self_tail k⟩⟩
    cases k 0 <;> simp

def realAbscissa (i : Fin 9) : Sun28.Branches.Poly 28 :=
  MvPolynomial.X (⟨2*i.val+1,by omega⟩ : Fin 28)
def radicalAbscissa (i : Fin 9) : Sun28.Branches.Poly 28 :=
  MvPolynomial.X (⟨2*i.val+2,by omega⟩ : Fin 28)

def nineRows : List (Sun28.Compiler.Branch 28) :=
  (patterns 9).map fun k => (sheet k realAbscissa radicalAbscissa).branch

theorem nine_signed_iff (p : Fin 28 → ℚ) (y : Fin 9 → K) :
    (∃ a : Fin 9 → AffineInput, ∀ i,
      (a i).re = p ⟨2*i.val+1,by omega⟩ ∧ (a i).im = p ⟨2*i.val+2,by omega⟩ ∧ (a i).y = y i) ↔
    ∃ (k : Fin 9 → Branch) (x : Fin 9 → ℚ),
      (sheet k realAbscissa radicalAbscissa).Holds (Sun28.Branches.value p) x ∧
      ∀ i, reads (Sun28.Branches.value p) x (ordinateOutputs k realAbscissa radicalAbscissa i) (y i) := by
  rw [← sheet_spec]
  let u (i : Fin 9) := p ⟨2*i.val+1,by omega⟩
  let v (i : Fin 9) := p ⟨2*i.val+2,by omega⟩
  have e (i : Fin 9) : curveTest (realAbscissa i) (radicalAbscissa i) (y i) (Sun28.Branches.value p) ↔
      (y i)^2 = (pair (u i) (v i))^3 - pair 11 (-6)*pair (u i) (v i) := by
    simp [curveTest,realAbscissa,radicalAbscissa,Sun28.Branches.value,u,v]
  constructor
  · rintro ⟨a,h⟩ i
    obtain ⟨hu,hv,hy⟩ := h i
    apply (e i).2
    apply (ordinate_charts ..).2
    exact ⟨(a i).branch,(a i).root,by simpa only [u,v,← hu,← hv] using (a i).valid,
      by simpa only [AffineInput.y,u,v,← hu,← hv] using hy.symm⟩
  · intro h
    have rep i := (ordinate_charts ..).1 ((e i).1 (h i))
    choose b t ht hy using rep
    exact ⟨fun i => ⟨u i,v i,b i,t i,ht i⟩,fun i => ⟨rfl,rfl,(hy i).symm⟩⟩

end
end Sun28.Concrete
#print axioms Sun28.Concrete.reads_lift
#print axioms Sun28.Concrete.sheet_spec
#print axioms Sun28.Concrete.mem_patterns
#print axioms Sun28.Concrete.nine_signed_iff
