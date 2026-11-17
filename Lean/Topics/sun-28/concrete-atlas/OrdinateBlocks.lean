import JointTests

/-! Polynomial blocks on the nine recovered points before elimination of tower roots. -/
namespace Sun28.Concrete
open Sun28.Ordinates Sun28.WitnessIndices Sun28.GroupCharts ZInQ
noncomputable section
variable {R : Type*} [CommRing R] {m n k : ℕ}

def pointOdd : PointCode R → TestBlock R
  | .affine x y => .odd x y
  | .infinity => .tests [] [0]

theorem point_odd_valid (φ : R →+* ℚ) {v : PointCode R} {P : CPoint} (hp : Represents φ v P) :
    (pointOdd v).Valid φ ↔ RationalOddChart P := by
  cases hp with
  | infinity => simp [pointOdd,TestBlock.Valid,RationalOddChart]
  | affine ht x y =>
    rw [odd_affine]
    change (_ ∧ _ ∧ oddRelation _ _) ↔ _
    rw [x.value,y.value]
    exact ⟨fun h => h.2.2, fun h => ⟨x.good,y.good,h⟩⟩

def panel (r : Concrete.Row (Base m) n) (f : Program (Test (Base m) n) (Fin k → TestBlock (Test (Base m) n))) :=
  f.rows.flatMap fun a => jointRows k a.output (r.tested a.equations a.guards)

theorem panel_spec (r : Concrete.Row (Base m) n) (f : Program (Test (Base m) n) (Fin k → TestBlock (Test (Base m) n)))
    (p : Fin m → ℚ) : Accepted (panel r f) p ↔ ∃ t, r.Holds (Sun28.Branches.value p) t ∧
      ∀ i, ((Program.eval (ev (Sun28.Branches.value p) t) f) i).Valid (ev (Sun28.Branches.value p) t) := by
  let φ := Sun28.Branches.value p
  rw [panel]
  constructor
  · rintro ⟨b,hb,hs⟩
    obtain ⟨a,ha,hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨t,hr,h⟩ := (joint_spec ..).1 ⟨b,hb,hs⟩
    obtain ⟨hh,he,hg⟩ := (tested_iff ..).1 hr
    have e := (Program.rows_correct (ev φ t) f a.output).1 ⟨a,ha,⟨he,hg⟩,rfl⟩
    exact ⟨t,hh,fun i => e.symm ▸ h i⟩
  · rintro ⟨t,hr,h⟩
    obtain ⟨a,ha,⟨he,hg⟩,ho⟩ := (Program.rows_correct (ev φ t) f _).2 rfl
    obtain ⟨b,hb,hs⟩ := (joint_spec k (r.tested a.equations a.guards) a.output p).2
      ⟨t,(tested_iff ..).2 ⟨hr,he,hg⟩,by rw [ho]; exact h⟩
    exact ⟨b,List.mem_flatMap.mpr ⟨a,ha,hb⟩,hs⟩

abbrev NineRing := Test (Base 28) 9
def rawPoint (b : Fin 9 → Branch) (i : Fin 9) : PointCode NineRing :=
  let q := ordinateOutputs b realAbscissa radicalAbscissa i
  .affine (.ofPair (MvPolynomial.C (realAbscissa i)) (MvPolynomial.C (radicalAbscissa i))) ⟨q.1,q.2.1,q.2.2⟩

private theorem read_ordinate (φ : R →+* ℚ) (t : Fin n → ℚ) (q : Triple (Test R n)) (y : K) :
    reads φ t q y ↔ Quad.Value (ev φ t) ⟨q.1,q.2.1,q.2.2⟩ y :=
  ⟨fun h => ⟨h.1,h.2.symm⟩,fun h => ⟨h.good,h.value.symm⟩⟩

/-- An individual accepted sheet determines all its signed outputs. -/
theorem sheet_total (φ : R →+* ℚ) (u v : Fin n → R) (b : Fin n → Branch) (t : Fin n → ℚ)
    (ht : (sheet b u v).Holds φ t) :
    ∀ i, ∃ y : K, reads φ t (ordinateOutputs b u v i) y := by
  induction n with
  | zero => exact fun i => i.elim0
  | succ n ih =>
    let s := Fin.tail t
    have e : Fin.cons (t 0) s = t := Fin.cons_self_tail _
    have h := (signed_iff (sheet (Fin.tail b) (Fin.tail u) (Fin.tail v)) φ s (t 0) (b 0)
      (MvPolynomial.C (RootCharts.realNumerator (u 0) (v 0))) (MvPolynomial.C (RootCharts.radicalNumerator (u 0) (v 0))) 1).1
      (by simpa only [e,sheet] using ht)
    refine Fin.cases ?_ (fun i => ?_)
    · obtain ⟨hr,hg,hw⟩ := h
      have out := (reads_output _ _ _ _ _ _ _ hg _).2 rfl
      exact ⟨_,by simpa only [e,ordinateOutputs,Fin.cons_zero] using out⟩
    · obtain ⟨y,hy⟩ := ih (Fin.tail u) (Fin.tail v) (Fin.tail b) s h.1 i
      exact ⟨y,by simpa only [e,ordinateOutputs,Fin.cons_succ] using (reads_lift φ s (t 0) _ _).2 hy⟩

def position (p : Fin 28 → ℚ) (a : Fin 9 → AffineInput) :=
  ∀ i, (a i).re = p ⟨2*i.val+1,by omega⟩ ∧ (a i).im = p ⟨2*i.val+2,by omega⟩

private theorem raw_spec {p : Fin 28 → ℚ} {k : Fin 9 → Branch} {t : Fin 9 → ℚ}
    {a : Fin 9 → AffineInput} (hp : position p a)
    (h : ∀ i, reads (Sun28.Branches.value p) t (ordinateOutputs k realAbscissa radicalAbscissa i) (a i).y) (i : Fin 9) :
    Represents (ev (Sun28.Branches.value p) t) (rawPoint k i) (a i).point := by
  apply PointCode.represents_affineInput
  · let f := ev (Sun28.Branches.value p) t
    refine ⟨Quad.good_pair f _ _,?_⟩
    simp [Quad.eval_pair,ev,realAbscissa,radicalAbscissa,Sun28.Branches.value,(hp i).1,(hp i).2,pair]
  · exact (read_ordinate ..).1 (h i)

def ordinatePanels {k : ℕ} (f : (Fin 9 → PointCode NineRing) → Program NineRing (Fin k → TestBlock NineRing)) :
    List (Sun28.Compiler.Branch 28) :=
  (patterns 9).flatMap fun b => panel (sheet b realAbscissa radicalAbscissa) (f (rawPoint b))

/-- Every accepted panel and its nine signed elliptic points use one tuple of rational parameters. -/
theorem ordinate_panels_spec {k : ℕ} (p : Fin 28 → ℚ)
    (f : (Fin 9 → PointCode NineRing) → Program NineRing (Fin k → TestBlock NineRing))
    (S : (Fin 9 → AffineInput) → Prop)
    (impl : ∀ (a : Fin 9 → AffineInput), position p a → ∀ (v : Fin 9 → PointCode NineRing) (t : Fin 9 → ℚ),
      (∀ i, Represents (ev (Sun28.Branches.value p) t) (v i) (a i).point) →
      ((∀ i, ((Program.eval (ev (Sun28.Branches.value p) t) (f v)) i).Valid (ev (Sun28.Branches.value p) t)) ↔ S a)) :
    Accepted (ordinatePanels f) p ↔ ∃ a, position p a ∧ S a := by
  rw [ordinatePanels,accepted_flat]
  constructor
  · rintro ⟨b,_,hb⟩
    obtain ⟨t,ht,hh⟩ := (panel_spec ..).1 hb
    choose y hy using sheet_total _ _ _ _ _ ht
    obtain ⟨a,ha⟩ := (nine_signed_iff p y).2 ⟨b,t,ht,hy⟩
    have hp : position p a := fun i => ⟨(ha i).1,(ha i).2.1⟩
    have e i := (ha i).2.2
    exact ⟨a,hp,(impl a hp _ t (raw_spec hp (fun i => (e i).symm ▸ hy i))).1 hh⟩
  · rintro ⟨a,hp,hs⟩
    obtain ⟨b,t,ht,hy⟩ := (nine_signed_iff p (fun i => (a i).y)).1
      ⟨a,fun i => ⟨(hp i).1,(hp i).2,rfl⟩⟩
    exact ⟨b,mem_patterns b,(panel_spec ..).2 ⟨t,ht,(impl a hp _ t (raw_spec hp hy)).2 hs⟩⟩

end
end Sun28.Concrete
#print axioms Sun28.Concrete.point_odd_valid
#print axioms Sun28.Concrete.panel_spec
#print axioms Sun28.Concrete.sheet_total
#print axioms Sun28.Concrete.ordinate_panels_spec
