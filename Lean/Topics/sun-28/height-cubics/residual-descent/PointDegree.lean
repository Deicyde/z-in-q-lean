import TraceLattice

namespace Sun28.FiveDescent.ResidueField
open IntermediateField NumberField Module
open private root_degree from FixedCurve
noncomputable section

theorem degree_cases {d e : ℤ} {r w : Omega} (hr:r^2=(d:Omega)) (hw:w^2=(e:Omega)) :
    finrank ℚ (coords r w)=1 ∨ finrank ℚ (coords r w)=2 ∨ finrank ℚ (coords r w)=4 := by
  let L:=coords r w
  let R:=adjoin ℚ ({r}:Set Omega)
  let W:=adjoin ℚ ({w}:Set Omega)
  have joined : R⊔W=L := by dsimp [R,W,L,coords];rw [←adjoin_union,Set.singleton_union]
  have dim : finrank ℚ L≤4 := by
    rw [←joined]
    exact (finrank_sup_le R W).trans (Nat.mul_le_mul (root_degree hr) (root_degree hw))
  have inc : R≤L := joined ▸ le_sup_left
  have rpos : 0<finrank ℚ R := finrank_pos
  have rdim : finrank ℚ R≤2 := root_degree hr
  have zero : 0<finrank ℚ L:=finrank_pos
  by_cases one : finrank ℚ R=1
  · have bot := finrank_eq_one_iff.mp one
    rw [bot,bot_sup_eq] at joined
    have b : finrank ℚ L≤2:=joined ▸ root_degree hw
    change finrank ℚ L=1 ∨ finrank ℚ L=2 ∨ finrank ℚ L=4
    omega
  · have two : finrank ℚ R=2 := by omega
    have dvd := finrank_dvd_of_le_right inc
    rw [two] at dvd
    change finrank ℚ L=1 ∨ finrank ℚ L=2 ∨ finrank ℚ L=4
    omega

theorem irrational_generators {d e : ℤ} {r w : Omega} (hr:r^2=(d:Omega)) (hw:w^2=(e:Omega))
    (rn:r≠0) (four:finrank ℚ (coords r w)=4) :
    r∉(⊥:IntermediateField ℚ Omega) ∧ w∉(⊥:IntermediateField ℚ Omega) ∧
    r*w∉(⊥:IntermediateField ℚ Omega) := by
  have binary {u v:Omega} {a:ℤ} (us:u^2=(a:Omega)) (mem:v∈adjoin ℚ ({u}:Set Omega)) :
      finrank ℚ (coords u v)≤2 := by
    have le : coords u v≤adjoin ℚ ({u}:Set Omega) := by
      apply adjoin_le_iff.mpr
      intro q h
      rcases Set.mem_insert_iff.mp h with eq|eq
      · exact eq ▸ mem_adjoin_simple_self ℚ u
      · exact Set.mem_singleton_iff.mp eq ▸ mem
    exact (finrank_le_of_le_right le).trans (root_degree us)
  have flip : coords w r=coords r w := by dsimp [coords];rw [Set.pair_comm]
  constructor
  · intro rb
    have D:=binary hw ((bot_le : (⊥:IntermediateField ℚ Omega)≤adjoin ℚ ({w}:Set Omega)) rb)
    rw [flip,four] at D;omega
  constructor
  · intro wb
    have D:=binary hr ((bot_le : (⊥:IntermediateField ℚ Omega)≤adjoin ℚ ({r}:Set Omega)) wb)
    omega
  · intro rb
    let R:=adjoin ℚ ({r}:Set Omega)
    have a : r*w∈R:= (bot_le : (⊥:IntermediateField ℚ Omega)≤R) rb
    have b : (r*w)/r∈R:=div_mem a (mem_adjoin_simple_self ℚ r)
    have wm : w∈R:=by simpa only [mul_div_cancel_left₀ _ rn] using b
    have D:=binary hr wm
    omega

end
end Sun28.FiveDescent.ResidueField
#print axioms Sun28.FiveDescent.ResidueField.degree_cases
#print axioms Sun28.FiveDescent.ResidueField.irrational_generators
