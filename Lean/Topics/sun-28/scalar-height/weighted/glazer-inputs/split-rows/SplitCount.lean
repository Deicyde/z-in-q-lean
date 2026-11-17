import SplitExceptions

/-! Count Glazer's exceptional slopes by a cone and a short real arc. -/
namespace ZInQBlueprint.SplitRows
open Finset ZInQBlueprint.OriginalHeightCount
open scoped Classical
attribute [local irreducible] Sun28.Ordinary.glazerConstant24 OriginalHeightCount.exceptions OriginalHeightCount.failure
set_option maxHeartbeats 120000
set_option maxRecDepth 12000
noncomputable section

abbrev Triple := ℕ × ℕ × ℕ
def key {x B K} (s : Record x B K) : Triple := (s.i,s.j,s.k)

abbrev Code := Chamber × Triple × ℕ
def code {x B K} (s : Record x B K) : Code := (ray x,key s,cell (size B) s.arc)

theorem same_code {x y z : ℚ} {B K : ℕ} (s : Record x B K)
    (t : Record y B K) (u : Record z B K)
    (eq₁ : code s=code t) (eq₂ : code s=code u) : x=y ∨ x=z ∨ y=z := by
  obtain ⟨i,j,k,P,p,ip,jp,kp,ic,jc,kc,hP,rP⟩:=s
  obtain ⟨i',j',k',Q,q,_,_,_,_,_,_,hQ,rQ⟩:=t
  obtain ⟨i'',j'',k'',R,r,_,_,_,_,_,_,hR,rR⟩:=u
  simp only [code,key,Prod.mk.injEq] at eq₁ eq₂
  obtain ⟨xy,⟨ii,jj,kk⟩,ct⟩:=eq₁
  obtain ⟨xz,⟨ii',jj',kk'⟩,cu⟩:=eq₂
  subst i'; subst j'; subst k'; subst i''; subst j''; subst k''
  let a : Record x B K := ⟨i,j,k,P,p,ip,jp,kp,ic,jc,kc,hP,rP⟩
  let b : Record y B K := ⟨i,j,k,Q,q,ip,jp,kp,ic,jc,kc,hQ,rQ⟩
  let c : Record z B K := ⟨i,j,k,R,r,ip,jp,kp,ic,jc,kc,hR,rR⟩
  have close := three_in_cell ip jp kp (H:=size B) (Nat.succ_pos _) p q r
    a.arc_bound b.arc_bound c.arc_bound ct cu
  change a.arc.t=b.arc.t ∨ a.arc.t=c.arc.t ∨ b.arc.t=c.arc.t at close
  have inj {v w : ℚ} (f : Record v B K) (g : Record w B K)
      (chamber : ray v=ray w) (same : f.arc.t=g.arc.t) : v=w := by
    apply value_injective chamber rfl
    calc
      value (ray w) (v:ℝ) = value (ray v) (v:ℝ) := congrArg (fun d=>value d (v:ℝ)) chamber.symm
      _ = _ := f.recover_arc
      _ = (2*g.arc.t/(1+g.arc.t^2))^2 := by rw [same]
      _ = value (ray w) (w:ℝ) := g.recover_arc.symm
  rcases close with h|h|h
  · exact Or.inl (inj a b xy h)
  · exact Or.inr (Or.inl (inj a c xz h))
  · exact Or.inr (Or.inr (inj b c (xy.symm.trans xz) h))

def codes (B : ℕ) (L : Finset Triple) : Finset Code :=
  (univ : Finset Chamber) ×ˢ (L ×ˢ range (3*size B))

theorem count_with_triples (S : Finset ℚ) {B K : ℕ} (L : Finset Triple)
    (rep : ∀ x∈S, ∃ s : Record x B K, key s∈L) :
    S.card ≤ 18*size B*L.card := by
  classical
  let pick (x : ℚ) (h : x∈S) := (rep x h).choose
  let f (x : ℚ) := if h:x∈S then code (pick x h) else (.middle,(0,0,0),0)
  have feq {x} (h:x∈S) : f x=code (pick x h) := dite_eq_left h
  have targets {x} (h:x∈S) : f x∈codes B L := by
    rw [feq h]
    exact mem_product.mpr ⟨mem_univ _,mem_product.mpr ⟨(rep x h).choose_spec,
      mem_range.mpr (cell_lt (Nat.succ_pos _) _)⟩⟩
  have fibres (c : Code) : (S.filter fun x=>f x=c).card≤2 := by
    by_contra! big
    obtain ⟨x,y,z,hx,hy,hz,xy,xz,yz⟩:=two_lt_card_iff.mp big
    obtain ⟨hsx,fx⟩:=mem_filter.mp hx
    obtain ⟨hsy,fy⟩:=mem_filter.mp hy
    obtain ⟨hsz,fz⟩:=mem_filter.mp hz
    rw [feq hsx] at fx
    rw [feq hsy] at fy
    rw [feq hsz] at fz
    rcases same_code (pick x hsx) (pick y hsy) (pick z hsz) (fx.trans fy.symm) (fx.trans fz.symm) with h|h|h
    · exact xy h
    · exact xz h
    · exact yz h
  calc
    S.card = ∑ c ∈ codes B L, (S.filter fun x=>f x=c).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ h=> targets h)
    _ ≤ ∑ _c ∈ codes B L, (2:ℕ) := Finset.sum_le_sum (fun c _=>fibres c)
    _ = 18*size B*L.card := by
      have chambers : (univ : Finset Chamber).card=3 := by decide
      simp only [sum_const,nsmul_eq_mul,Nat.cast_id,codes,card_product,card_range,chambers];ring

theorem exception_count {B K : ℕ} (threshold : Real.log (B:ℝ) ≤ ((K+1:ℕ):ℝ)^24) :
    (exceptions B).card ≤ 18*((2*B).sqrt+1)*K^3 := by
  let I:=Icc 1 K
  let L:=I ×ˢ (I ×ˢ I)
  have card : L.card=K^3 := by simp [L,I,Nat.card_Icc];ring
  rw [←card]
  apply count_with_triples (B:=B) (K:=K)
  intro x hx
  obtain ⟨s⟩:=record_at_failure hx threshold
  exact ⟨s,mem_product.mpr ⟨mem_Icc.mpr ⟨s.ip,s.ic⟩,mem_product.mpr
    ⟨mem_Icc.mpr ⟨s.jp,s.jc⟩,mem_Icc.mpr ⟨s.kp,s.kc⟩⟩⟩⟩

end
end ZInQBlueprint.SplitRows
#print axioms ZInQBlueprint.SplitRows.same_code
#print axioms ZInQBlueprint.SplitRows.count_with_triples
#print axioms ZInQBlueprint.SplitRows.exception_count
