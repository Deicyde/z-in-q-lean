import OddAtlas

/-! Test the fixed point data together. All later conditions use the original tuple. -/
namespace Sun28.Concrete
open Sun28.Ordinates Sun28.GroupCharts Sun28.WitnessIndices ZInQ
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}

inductive TestBlock (R : Type*) where
  | tests (E G : List R)
  | odd (x y : Quad R)
  | pole (p : PoleData R)

def TestBlock.map (f : R →+* S) : TestBlock R → TestBlock S
  | .tests E G => .tests (E.map f) (G.map f)
  | .odd x y => .odd (x.map f) (y.map f)
  | .pole p => .pole ⟨f p.num,f p.den,f p.e,f p.z⟩

def TestBlock.Valid (f : R →+* ℚ) : TestBlock R → Prop
  | .tests E G => (∀ e∈E,f e=0) ∧ ∀ g∈G,f g≠0
  | .odd x y => x.Good f ∧ y.Good f ∧ oddRelation (x.eval f) (y.eval f)
  | .pole p => f p.den≠0 ∧ Sun28.Forward.poleAt Sun28.ScalarHeight.smallMultipliers (f p.num/f p.den) (f p.e) (f p.z)

theorem block_map (b : TestBlock R) (g : R →+* S) (f : S →+* ℚ) :
    (b.map g).Valid f ↔ b.Valid (f.comp g) := by
  cases b with
  | tests E G => simp [TestBlock.map,TestBlock.Valid]
  | odd x y => rfl
  | pole p => rfl

def up2 {R : Type*} [CommRing R] (n : ℕ) := (liftRoot (R:=R) (n+1)).comp (liftRoot n)
def up3 {R : Type*} [CommRing R] (n : ℕ) := (liftRoot (R:=R) (n+2)).comp (up2 n)

def triples : List (Branch × Branch × Branch) :=
  let l := [Branch.mixed,.realPart,.radicalPart,.zero]
  l.flatMap fun b => l.flatMap fun c => l.map (fun d => (b,c,d))

theorem mem_triples (b c d : Branch) : (b,c,d)∈triples := by
  have h (a : Branch) : a ∈ [Branch.mixed,.realPart,.radicalPart,.zero] := by cases a <;> simp
  exact List.mem_flatMap.mpr ⟨b,h b,List.mem_flatMap.mpr ⟨c,h c,List.mem_map.mpr ⟨d,h d,rfl⟩⟩⟩

abbrev Base (m : ℕ) := Sun28.Branches.Poly m

def jointRows : (k : ℕ) → {n : ℕ} → (Fin k → TestBlock (Test (Base m) n)) →
    Concrete.Row (Base m) n → List (Sun28.Compiler.Branch m)
  | 0,_,_,r => [r.branch]
  | k+1,n,f,r =>
    let rest := Fin.tail f
    match f 0 with
    | .tests E G => jointRows k rest (r.tested E G)
    | .pole p => jointRows k rest (zeroPole r p) ++ poleMultipliers.flatMap fun j =>
        jointRows k (fun i => (rest i).map (up2 n)) (nonzeroPole r p j)
    | .odd x y =>
        let start := r.tested [] [x.den,y.den]
        triples.flatMap fun (b,c,d) =>
          jointRows k (fun i => (rest i).map (up3 n)) (oddRows start x y b c d)

private theorem block_two (φ : R →+* ℚ) (t : Fin n → ℚ) (u w : ℚ) (b : TestBlock (Test R n)) :
    (b.map (up2 n)).Valid (ev φ (Fin.cons w (Fin.cons u t))) ↔ b.Valid (ev φ t) := by
  rw [block_map,up2,← RingHom.comp_assoc,eval_liftRoot,eval_liftRoot]

private theorem block_three (φ : R →+* ℚ) (t : Fin n → ℚ) (u w z : ℚ) (b : TestBlock (Test R n)) :
    (b.map (up3 n)).Valid (ev φ (Fin.cons z (Fin.cons w (Fin.cons u t)))) ↔ b.Valid (ev φ t) := by
  rw [block_map,up3,← RingHom.comp_assoc,eval_liftRoot,← block_map,block_two]

private theorem odds_start (r : Concrete.Row R n) (x y : QuadAt R n) (φ : R →+* ℚ) (t : Fin n → ℚ) :
    (r.tested [] [x.den,y.den]).Holds φ t ↔ r.Holds φ t ∧ x.Good (ev φ t) ∧ y.Good (ev φ t) := by
  rw [tested_iff]
  simp [Quad.Good]

private theorem odd_block (r : Concrete.Row R n) (x y : QuadAt R n) (φ : R →+* ℚ) (t : Fin n → ℚ) :
    (r.Holds φ t ∧ (TestBlock.odd x y).Valid (ev φ t)) ↔
    ∃ (b c d : Branch) (s w z : ℚ), (oddRows (r.tested [] [x.den,y.den]) x y b c d).Holds φ
      (Fin.cons z (Fin.cons w (Fin.cons s t))) := by
  constructor
  · rintro ⟨hr,hx,hy,ho⟩
    exact (odd_rows_spec _ _ _ _ _ ⟨hx,rfl⟩ ⟨hy,rfl⟩).1 ⟨(odds_start ..).2 ⟨hr,hx,hy⟩,ho⟩
  · rintro ⟨b,c,d,s,w,z,hs⟩
    have hh := hs
    simp only [oddRows,squareRow,signed_iff] at hh
    have h := (odds_start r x y φ t).1 (show (r.tested [] [x.den,y.den]).Holds φ t from by
      have h' := (tested_iff ..).1 hh.1.1
      exact ((signed_iff ..).1 h'.1).1)
    exact ⟨h.1,h.2.1,h.2.2,((odd_rows_spec _ _ _ _ _ ⟨h.2.1,rfl⟩ ⟨h.2.2,rfl⟩).2 ⟨b,c,d,s,w,z,hs⟩).2⟩

def Accepted (bs : List (Sun28.Compiler.Branch m)) (p : Fin m → ℚ) : Prop :=
  ∃ b ∈ bs, Sun28.Compiler.Solutions b.tower b.equations b.guards p

theorem accepted_flat {α : Type*} (l : List α) (g : α → List (Sun28.Compiler.Branch m)) (p : Fin m → ℚ) :
    Accepted (l.flatMap g) p ↔ ∃ a∈l, Accepted (g a) p := by
  simp only [Accepted,List.mem_flatMap]
  constructor
  · rintro ⟨b,⟨a,ha,hb⟩,hs⟩
    exact ⟨a,ha,b,hb,hs⟩
  · rintro ⟨a,ha,b,hb,hs⟩
    exact ⟨b,⟨a,ha,hb⟩,hs⟩

private theorem accepted_append (a b : List (Sun28.Compiler.Branch m)) (p : Fin m → ℚ) :
    Accepted (a++b) p ↔ Accepted a p ∨ Accepted b p := by
  simp only [Accepted,List.mem_append]
  aesop


theorem joint_spec (k : ℕ) (r : Concrete.Row (Base m) n)
    (b : Fin k → TestBlock (Test (Base m) n)) (p : Fin m → ℚ) :
    Accepted (jointRows k b r) p ↔ ∃ t, r.Holds (Sun28.Branches.value p) t ∧
      ∀ i, (b i).Valid (ev (Sun28.Branches.value p) t) := by
  let φ := Sun28.Branches.value p
  induction k generalizing n with
  | zero =>
    simpa [jointRows,Accepted] using row_solutions r p
  | succ k ih =>
    rw [jointRows]
    cases z : b 0 with
    | tests E G =>
      simp only [ih,tested_iff]
      constructor
      · rintro ⟨t,⟨hr,he,hg⟩,ht⟩
        exact ⟨t,hr,Fin.cases (by rw [z]; exact ⟨he,hg⟩) ht⟩
      · rintro ⟨t,hr,h⟩
        have hz := h 0
        rw [z] at hz
        exact ⟨t,⟨hr,hz.1,hz.2⟩,fun i => h i.succ⟩
    | pole a =>
      simp only [accepted_append,accepted_flat,ih]
      constructor
      · rintro (⟨t,hr,ht⟩ | ⟨j,hj,T,hT,hb⟩)
        · obtain ⟨h,hd,hz⟩ := (zero_pole_iff ..).1 hr
          exact ⟨t,h,Fin.cases (by rw [z]; exact ⟨hd,Or.inl hz⟩) ht⟩
        · let t := Fin.tail (Fin.tail T)
          have pack : Fin.cons (T 0) (Fin.cons (Fin.tail T 0) t) = T := by simp [t]
          obtain ⟨hr,hd,hp⟩ := (nonzero_pole_iff r φ t a j).1 ⟨_,_,pack ▸ hT⟩
          refine ⟨t,hr,Fin.cases (by rw [z]; exact ⟨hd,Or.inr ⟨_,(multiplier_mem _).2 ⟨j,hj,rfl⟩,hp⟩⟩) ?_⟩
          intro i
          exact (block_two φ t (Fin.tail T 0) (T 0) _).1 (pack ▸ hb i)
      · rintro ⟨t,hr,h⟩
        have hz := h 0
        rw [z] at hz
        obtain ⟨hd,hz|⟨q,hq,hp⟩⟩ := hz
        · exact Or.inl ⟨t,(zero_pole_iff ..).2 ⟨hr,hd,hz⟩,fun i => h i.succ⟩
        · obtain ⟨j,hj,rfl⟩ := (multiplier_mem q).1 hq
          obtain ⟨s,w,hs⟩ := (nonzero_pole_iff r φ t a j).2 ⟨hr,hd,hp⟩
          exact Or.inr ⟨j,hj,_,hs,fun i => (block_two ..).2 (h i.succ)⟩
    | odd x y =>
      simp only [accepted_flat,ih]
      constructor
      · rintro ⟨⟨b₁,b₂,b₃⟩,_,T,hT,hb⟩
        let t := Fin.tail (Fin.tail (Fin.tail T))
        let s := Fin.tail (Fin.tail T) 0
        let w := Fin.tail T 0
        have pack : Fin.cons (T 0) (Fin.cons w (Fin.cons s t)) = T := by simp [t,s,w]
        obtain ⟨hr,ho⟩ := (odd_block r x y φ t).2 ⟨b₁,b₂,b₃,s,w,T 0,pack ▸ hT⟩
        refine ⟨t,hr,Fin.cases (by rw [z]; exact ho) ?_⟩
        intro i
        exact (block_three φ t s w (T 0) _).1 (pack ▸ hb i)
      · rintro ⟨t,hr,h⟩
        have ho := h 0
        rw [z] at ho
        obtain ⟨b₁,b₂,b₃,s,w,z',hs⟩ := (odd_block r x y φ t).1 ⟨hr,ho⟩
        exact ⟨⟨b₁,b₂,b₃⟩,mem_triples ..,_,hs,fun i => (block_three ..).2 (h i.succ)⟩

end
end Sun28.Concrete
#print axioms Sun28.Concrete.block_map
#print axioms Sun28.Concrete.mem_triples
#print axioms Sun28.Concrete.joint_spec
