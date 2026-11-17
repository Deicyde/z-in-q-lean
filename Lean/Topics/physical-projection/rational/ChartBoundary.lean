import ChartSupport
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem t_congr (k : DBlock) {a b : Assignment} (h : ∀ i,earlySlots.contains i=true → a i=b i) : k.t a=k.t b := by
  have x:=h 32 (by decide);have y:=h 145 (by decide);have z:=h 157 (by decide)
  cases k <;> simp [DBlock.t,x,y,z]

theorem t_before (g : Bool) (y : Fin 130→Rat) (z : Assignment) (ok : ∀p∈ps g,p.ok z)
    (h : ∀ i, earlySlots.contains i=true → i∉slots (ps g) → seed130 y i=z i) (k : DBlock) :
    k.t (preliminary g y)=k.t z := by
  have r:=recov_on (ps g) earlySlots.contains (seed130 y) z (good0 g) (physical_early g) h
  rw [Triangular.fixed (ps g) (good0 g) z ok] at r
  exact t_congr k r

theorem point_t (g : Bool) (y : Fin 130→Rat) (k : DBlock) :
    k.t (chartPoint g y)=k.t (preliminary g y) := by
  have untouched : earlySlots.all (fun i => !(changed++padeSlots).contains i)=true := by decide
  have disjoint (i : Nat) (h : earlySlots.contains i=true) : i∉changed ∧ i∉padeSlots := by
    simpa using List.all_eq_true.mp untouched i (by simpa using h)
  have med:=recov_on (ps g) earlySlots.contains (detectorSeed (preliminary g y) (seed130 y))
    (seed130 y) (good0 g) (physical_early g) (fun i h _ => detectorSeed_keep _ _ (disjoint i h).1)
  apply t_congr; intro i hi
  exact (fillPairs_keep (middle g y) (disjoint i hi).2).trans (med i hi)

theorem point_free (g : Bool) (y : Fin 130→Rat) {i : Nat} (hp : i∉padeSlots) (hf : i∉slots (ps g)) :
    chartPoint g y i=detectorSeed (preliminary g y) (seed130 y) i :=
  (fillPairs_keep _ hp).trans (middle_free g y hf)

theorem point_detector (g : Bool) (y : Fin 130→Rat) (k : DBlock) :
    let x:=chartPoint g y; let pre:=preliminary g y; let s:=seed130 y
    x k.e=s k.e ∧ x (k.e+1)=k.a s ∧ x (k.e+5)=k.q s ∧ x (k.e+6)=k.bigQ pre s := by
  dsimp only
  have get (i : Nat) (safe : i∈changed++[135,147,159]) (notPair : i∉padeSlots) :=
    point_free g y notPair (no_hidden_pivot g (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at safe ⊢; grind))
  cases k <;> simp only [DBlock.e] <;>
    repeat' apply And.intro
  all_goals apply Eq.trans (get _ (by decide) (by decide)); rfl

theorem guard_values_iff (g : Bool) (y : Fin 130→Rat) :
    (∀v∈guardValues g y,v=0) ↔ ∀k : DBlock,k.guard (preliminary g y) (seed130 y)=0 := by
  constructor
  · intro h k; apply h; apply List.mem_map.mpr;exact ⟨k,by cases k <;> decide,rfl⟩
  · intro h v hv;obtain ⟨k,_,rfl⟩:=List.mem_map.mp hv;exact h k

theorem point_input (g : Bool) (y : Fin 130→Rat) : chartPoint g y 1=finiteLift y 1 := by
  exact (point_free g y (by decide) (no_hidden_pivot g (by decide))).trans (seed_at_input y)

theorem point_outside (g : Bool) (y : Fin 130→Rat) {i : Nat} (hi : inside i=false) : chartPoint g y i=0 := by
  have c : (parentSlots++changed++padeSlots).all inside=true := by decide
  have away : i∉parentSlots ∧ i∉changed ∧ i∉padeSlots := by
    have n : i∉parentSlots++changed++padeSlots := by intro v; have h:=List.all_eq_true.mp c i v;rw [hi] at h;contradiction
    simpa using n
  rw [point_free g y away.2.2 (outside_pivots g hi),detectorSeed_keep _ _ away.2.1,seed_missing _ _ away.1]

end PhysicalProjection
