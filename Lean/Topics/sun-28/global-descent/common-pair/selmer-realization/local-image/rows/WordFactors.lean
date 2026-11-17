import LocalSymbols

namespace Sun28.FixedLocalRows

/-- Deleting one generator replaces it by 1, so the positions of all
remaining exponent bits stay fixed. -/
theorem insert_factor (p : ℤ) (s : List ℤ) (j i : Nat) (v : Word)
    (distinct : s.Nodup) (atj : s[j]? = some p) :
    generatorProduct s i v =
       p ^ (v.getLsbD (i+j)).toNat *
         generatorProduct (s.map (fun a => if a=p then 1 else a)) i v := by
  induction s generalizing j i with
  | nil => simp at atj
  | cons a s ih =>
    obtain ⟨different, rest⟩ := List.nodup_cons.mp distinct
    cases j with
    | zero =>
      have ap : a=p := by simpa using atj
      subst a
      have rem : s.map (fun a => if a=p then (1:ℤ) else a) = s := by
        have h : s.map (fun a => if a=p then (1:ℤ) else a) = s.map id := by
          apply List.map_congr_left
          intro x mem
          simp [show x≠p from fun e=>different (e ▸ mem)]
        simpa using h
      cases h : v.getLsbD i <;> simp [generatorProduct,h,rem]
    | succ k =>
      have pos : s[k]? = some p := by simpa using atj
      have pm : p∈s := List.mem_of_getElem? pos
      have ap : a≠p := fun h => different (h ▸ pm)
      have eq := ih k (i+1) rest pos
      simp only [generatorProduct,List.map_cons,ap,ite_false]
      rw [eq]
      have hi : i+(k+1)=i+1+k := by omega
      rw [hi]
      ac_rfl

end Sun28.FixedLocalRows
#print axioms Sun28.FixedLocalRows.insert_factor
