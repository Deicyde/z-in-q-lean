import QuadProgram

namespace Sun28.GroupCharts

/-- Branch on a single rational polynomial tested for zero. -/
inductive Program (R α : Type*) where
  | pure (x : α)
  | branch (guard : R) (zero nonzero : Program R α)

namespace Program
variable {R α β : Type*}

def bind (f : α → Program R β) : Program R α → Program R β
  | .pure x => f x
  | .branch g z n => .branch g (bind f z) (bind f n)

def eval [CommRing R] (φ : R →+* ℚ) : Program R α → α
  | .pure x => x
  | .branch g z n => if φ g=0 then eval φ z else eval φ n

@[simp] theorem eval_bind [CommRing R] (φ : R →+* ℚ) (f : α → Program R β) (p : Program R α) :
    eval φ (bind f p)=eval φ (f (eval φ p)) := by
  induction p with
  | pure => rfl
  | branch g z n hz hn => by_cases hg : φ g=0 <;> simp [bind,eval,hg,hz,hn]

/-- Each leaf is an output accompanied by the equality and inequation guards along its path. -/
def rows : Program R α → List (Row R α)
  | .pure x => [Row.pure x]
  | .branch g z n =>
    (rows z).map (Row.join (⟨[g],[],()⟩ : Row R Unit)) ++
    (rows n).map (Row.join (⟨[],[g],()⟩ : Row R Unit))

private theorem runs_map [CommRing R] (φ : R →+* ℚ) (r : Row R Unit) (xs : List (Row R α)) (a : α) :
    Row.Runs φ (xs.map (Row.join r)) a ↔ r.Live φ ∧ Row.Runs φ xs a := by
  constructor
  · rintro ⟨_,he,hv,ho⟩
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp he
    obtain ⟨prev,next⟩ := (Row.live_join ..).1 hv
    exact ⟨prev,s,hs,next,ho⟩
  · rintro ⟨hr,s,hs,hv,ho⟩
    exact ⟨r.join s,List.mem_map.mpr ⟨s,hs,rfl⟩,(Row.live_join ..).2 ⟨hr,hv⟩,ho⟩

private theorem runs_append [CommRing R] (φ : R →+* ℚ) (xs ys : List (Row R α)) (a : α) :
    Row.Runs φ (xs++ys) a ↔ Row.Runs φ xs a ∨ Row.Runs φ ys a := by
  simp only [Row.Runs,List.mem_append]
  aesop

theorem rows_correct [CommRing R] (φ : R →+* ℚ) (p : Program R α) (a : α) :
    Row.Runs φ p.rows a ↔ eval φ p=a := by
  induction p with
  | pure x => simp [rows,Row.Runs,Row.pure,Row.Live,eval]
  | branch g z n hz hn =>
    rw [rows,runs_append,runs_map,runs_map,hz,hn]
    by_cases hg : φ g=0 <;> simp [Row.Live,eval,hg]

end Program
#print axioms Program.rows_correct
end Sun28.GroupCharts
