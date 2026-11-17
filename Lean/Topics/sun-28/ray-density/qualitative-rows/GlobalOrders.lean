import AnchorOrders

namespace Sun28.QualitativeRows
theorem balanced_of_global {ι J : Type*} [Fintype ι] [Fintype J]
    (orders : ι→Bool→ℕ) (m r : J→ℕ) (C : ℕ)
    (orderPos : ∀ i s,0<orders i s) (mp : ∀ j,0<m j)
    (base : ∀ i j,r i ≡ r j [MOD (m i).gcd (m j)]) (x : ι→Bool) (h : ℤ)
    (fixed : ∀ j,h ≡ (r j:ℤ) [ZMOD (m j:ℤ)])
    (left : ∀ i,h ≡ 0 [ZMOD (orders i (x i):ℤ)])
    (right : ∀ i,h ≡ (C:ℤ) [ZMOD (orders i (!(x i)):ℤ)]) :
    ∀ v,¬Walk (Edge orders m r C) v v true := by
  classical
  have nz (i : J ⊕ (ι × Bool)) : 0 < comparisonMod orders m i := by
    cases i with
    | inl j => exact mp j
    | inr i => exact orderPos i.1 i.2
  have solved (i : J ⊕ (ι × Bool)) :
      h ≡ (comparisonRes C r x i:ℤ) [ZMOD (comparisonMod orders m i:ℤ)] := by
    rcases i with j | ⟨i,s⟩
    · exact fixed j
    · cases e : x i <;> cases s
      · simpa [comparisonMod,comparisonRes,e] using left i
      · simpa [comparisonMod,comparisonRes,e] using right i
      · simpa [comparisonMod,comparisonRes,e] using right i
      · simpa [comparisonMod,comparisonRes,e] using left i
  have comp := (CRT.exists_iff Finset.univ (comparisonMod orders m) (comparisonRes C r x)
    (fun i _ => nz i)).mp ⟨h,fun i _ => solved i⟩
  apply (balanced_iff (Edge orders m r C) (fun e=>edge_symm e)).mp
  refine ⟨fun v=>v.elim false x,?_⟩
  intro u v d e
  exact (edge_iff orders m r C x base).mpr (fun i j=>comp i (Finset.mem_univ _) j (Finset.mem_univ _)) e
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.balanced_of_global
