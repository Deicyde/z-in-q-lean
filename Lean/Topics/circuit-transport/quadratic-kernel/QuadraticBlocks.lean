import QuadraticPivots
import PairProjection

namespace CircuitTransport.Quadratic

/-- Two rationally scaled rows of multiplication by `a+b√2`, with given right sides. -/
structure RowPair where
  a : Rat
  b : Rat
  scale₁ : Rat
  scale₂ : Rat
  right₁ : Rat
  right₂ : Rat

def RowPair.block (r : RowPair) : Pair.Block :=
  ⟨r.scale₁*r.a, r.scale₁*(2*r.b), r.scale₂*r.b, r.scale₂*r.a, r.right₁, r.right₂⟩

def ProperScales (rows : List RowPair) := ∀ r∈rows, r.scale₁≠0 ∧ r.scale₂≠0

/-- A finite list of such paired rows has the precise hypothesis of `Pair.adjugate_iff`. -/
theorem blocks_no_rank_one (rows : List RowPair) (proper : ProperScales rows) :
    Pair.NoRankOne (rows.map RowPair.block) := by
  intro B mem singular
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp mem
  obtain ⟨one,two⟩ := proper r hr
  exact scaled_no_rank_one r.a r.b r.scale₁ r.scale₂ one two singular

/-- The paired polynomial for these multipliers needs no additional hypothesis on the matrices. -/
theorem paired_quadratic_iff (rows : List RowPair) (proper : ProperScales rows) (a b c d : Rat) :
    let bs := rows.map RowPair.block
    (∃ u v : Rat, Pair.pairValue bs a b c d u v=0) ↔
      Pair.Consistent bs ∧ Pair.Roots a b ∧ Pair.Roots c d :=
  Pair.pairValue_iff (blocks_no_rank_one rows proper) a b c d

#print axioms blocks_no_rank_one
#print axioms paired_quadratic_iff

end CircuitTransport.Quadratic
