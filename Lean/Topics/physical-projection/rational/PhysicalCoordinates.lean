import ChartBoundary
import ChartCoverage
import PadeRecovery
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 15000
set_option maxHeartbeats 1500000

def encoded (x : Assignment) (u : DBlock→Rat) (i : Nat) : Rat :=
  if i=136 then u .one else if i=148 then u .two else if i=160 then u .three else x i

def candidate (x : Assignment) (u : DBlock→Rat) := pack (encoded x u)

def fits (k : DBlock) (x : Assignment) (u : Rat) : Prop :=
  let e:=x k.e; let s:=1-e*(k.den*k.t x)*u
  e*s=0 ∧ x (k.e+1)= -(k.den*e*u)^3 ∧ x (k.e+5)=e^19*x (k.e+1) ∧
  x (k.e+6)=e^79*x (k.e+1)+s*u

theorem early_retained (g : Bool) {i : Nat} (early : earlySlots.contains i=true) (free : i∉slots (ps g)) :
    i∈parentSlots ∧ i∉ports := by
  have t : earlySlots.all (fun j => (slots (ps g)).contains j || (parentSlots.contains j && !ports.contains j))=true := by
    unfold ps; rw [slots0]; decide
  have v := List.all_eq_true.mp t i (by simpa using early)
  simpa [free] using v

theorem encoded_keep {i : Nat} (v : i∉ports) (x : Assignment) (u : DBlock→Rat) : encoded x u i=x i := by
  simp [ports] at v; simp [encoded,v]

theorem candidate_get (x : Assignment) (u : DBlock→Rat) (k : DBlock) :
    seed130 (candidate x u) k.e=x k.e ∧ seed130 (candidate x u) (k.e+1)=u k := by
  cases k <;> constructor <;> exact (seed_pack _ _ (by decide)).trans (by rfl)

theorem candidate_pre (g : Bool) (x : Assignment) (u : DBlock→Rat) (hp : pivotOK g x) (k : DBlock) :
    k.t (preliminary g (candidate x u))=k.t x := by
  apply t_before g _ x hp _ k
  intro i hie free
  obtain ⟨keep,untouched⟩ := early_retained g hie free
  exact (seed_pack _ _ keep).trans (encoded_keep untouched _ _)

theorem candidate_values (g : Bool) (x : Assignment) (u : DBlock→Rat) (hp : pivotOK g x)
    (hs : ∀k,fits k x (u k)) (k : DBlock) :
    let y:=candidate x u;let seed:=seed130 y;let prelim:=preliminary g y
    k.guard prelim seed=0 ∧ k.a seed=x (k.e+1) ∧ k.q seed=x (k.e+5) ∧ k.bigQ prelim seed=x (k.e+6) := by
  dsimp only
  let y:=candidate x u
  have old:=hs k; obtain ⟨hg,ha,hq,hQ⟩:=old
  obtain ⟨e,reg⟩:=candidate_get x u k
  simp only [DBlock.guard,DBlock.a,DBlock.q,DBlock.bigQ,DBlock.sl,e,reg,candidate_pre g x u hp,←ha]
  exact ⟨hg,True.intro,hq.symm,hQ.symm⟩

theorem candidate_modified (g : Bool) (x : Assignment) (u : DBlock→Rat) (hp : pivotOK g x) (hs : ∀k,fits k x (u k))
    {i : Nat} (h : i∈changed) :
    detectorSeed (preliminary g (candidate x u)) (seed130 (candidate x u)) i=x i := by
  have a:=candidate_values g x u hp hs .one;have b:=candidate_values g x u hp hs .two;have c:=candidate_values g x u hp hs .three
  simp [changed] at h
  rcases h with h|h|h|h|h|h|h|h|h <;> subst i
  · exact a.2.1
  · exact a.2.2.1
  · exact a.2.2.2
  · exact b.2.1
  · exact b.2.2.1
  · exact b.2.2.2
  · exact c.2.1
  · exact c.2.2.1
  · exact c.2.2.2

theorem candidate_middle (g : Bool) (x : Assignment) (u : DBlock→Rat) (hp : pivotOK g x) (hs : ∀k,fits k x (u k))
    (out : ∀ i,inside i=false → x i=0) :
    ∀ i, visible i=true → middle g (candidate x u) i=x i := by
  let y:=candidate x u
  have initial (i : Nat) (hi : visible i=true) (free : i∉slots (ps g)) : detectorSeed (preliminary g y) (seed130 y) i=x i := by
    by_cases use : i∈changed
    · exact candidate_modified g x u hp hs use
    · rw [detectorSeed_keep _ _ use]
      by_cases within : inside i=true
      · have belongs:=covered g within hi free use
        have notport : i∉ports := by intro p; apply use; simp [ports] at p; simp [changed];grind
        exact (seed_pack _ _ belongs).trans (encoded_keep notport _ _)
      · have lies : parentSlots.all inside=true := by decide
        have miss : i∉parentSlots := fun h => within (List.all_eq_true.mp lies i h)
        rw [seed_missing _ _ miss,out i (by simpa using within)]
  have r:=recov_on (ps g) visible (detectorSeed (preliminary g y) (seed130 y)) x (good0 g) (fun p h _ => (physical_visible g p h).2) initial
  rw [Triangular.fixed (ps g) (good0 g) x hp] at r
  exact r

theorem chart_agrees (g : Bool) (x : Assignment) (u : DBlock→Rat) (hp : pivotOK g x) (hs : ∀k,fits k x (u k))
    (pairsHold : ∀ k : PPair, value x k.f=0 ∧ value x k.g=0) (out : ∀ i,inside i=false → x i=0) :
    off privateSlots x (chartPoint g (candidate x u)) := by
  let y:=candidate x u
  have base:=candidate_middle g x u hp hs out
  have same (k : PPair) : k.U (middle g y)=x k.slot ∧ k.V (middle g y)=x (k.slot+1) := by
    obtain ⟨uf,vf⟩ := uv_agree k (fun i hi => base i (pair_support_visible k i hi))
    obtain ⟨us,vs⟩ := (pade_iff g k x hp).mp (pairsHold k)
    exact ⟨uf.trans us,vf.trans vs⟩
  intro i hi
  by_cases p : i∈padeSlots
  · simp [padeSlots] at p
    rcases p with r|r|r|r|r|r|r|r <;> subst i
    · exact (fill_U .one _).trans (same .one).1
    · exact (fill_V .one _).trans (same .one).2
    · exact (fill_U .two _).trans (same .two).1
    · exact (fill_V .two _).trans (same .two).2
    · exact (fill_U .three _).trans (same .three).1
    · exact (fill_V .three _).trans (same .three).2
    · exact (fill_U .four _).trans (same .four).1
    · exact (fill_V .four _).trans (same .four).2
  · exact (fillPairs_keep _ p).trans (base i (by simp [visible,apart,hi,p]))

end PhysicalProjection
