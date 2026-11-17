import SignedRows

namespace Sun28.CommonRows
open Finset Filter Sun28.PrimeValues Sun28.FinitePattern Sun28.PrimeClasses
open Sun28.PrimeLower Sun28.ContactFactors Sun28.ContactSieve Sun28.WeightedSelection
open Sun28.SinglePrime Sun28.MediumSieve Sun28.MixedSieve Sun28.PrimeMass
open Sun28.GaussianSelection
open ManuscriptV15.Arithmetic
open scoped Classical
noncomputable section

private theorem mark {p:ℕ} [Fact p.Prime] (inert:p%4=3) (e:Bool) (z:Circle p 1) :
    z∈bad p 1 e ↔ z.val=(if e then (-1,0) else (1,0)) := by
  have zero (a b:ZMod p) (h : a^2+b^2=0) : a=0 ∧ b=0 := by
    have eq : a^2 = -b^2 := eq_neg_of_add_eq_zero_left h
    have bz : b=0 := by
      by_contra ne
      exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' ne eq inert
    exact ⟨by simpa [bz] using eq,bz⟩
  cases e
  · change z∈Finset.univ.filter _ ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Bool.false_eq_true,ite_false]
    constructor
    · intro h
      change (z.val.1+ -1)^2+z.val.2^2=0 at h
      obtain ⟨x,y⟩:=zero _ _ h
      exact Prod.ext (by dsimp;linear_combination x) y
    · intro h
      change (z.val.1+ -1)^2+z.val.2^2=0
      rw [h];norm_num
  · change z∈Finset.univ.filter _ ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,ite_true]
    constructor
    · intro h
      change (z.val.1+1)^2+z.val.2^2=0 at h
      obtain ⟨x,y⟩:=zero _ _ h
      exact Prod.ext (by dsimp;linear_combination x) y
    · intro h
      change (z.val.1+1)^2+z.val.2^2=0
      rw [h];norm_num

private theorem circle_size {p:ℕ} [Fact p.Prime] (inert:p%4=3) :
    Fintype.card (Circle p 1)=p+1 := by
  have odd : p≠2 := by omega
  have h:=circle_card (p:=p) (t:=1) odd one_ne_zero
  rw [legendreSym.at_neg_one odd,ZMod.χ₄_nat_eq_if_mod_four] at h
  have modn : p%2≠0 := by omega
  have ns : p%4≠1 := by omega
  simp [inert,modn] at h
  omega

private theorem finite_boxes {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (a b:α) (ab:a≠b) : 
    (((Finset.univ.filter fun z:ι→α=> (∀i,z i≠a) ∨ (∀i,z i≠b)).card:ℤ)) =
      2*((Fintype.card α-1:ℕ):ℤ)^(Fintype.card ι)-
        ((Fintype.card α-2:ℕ):ℤ)^(Fintype.card ι) := by
  classical
  let L:=Fintype.piFinset (fun _ : ι=>({a}:Finset α)ᶜ)
  let R:=Fintype.piFinset (fun _ : ι=>({b}:Finset α)ᶜ)
  have un : (univ.filter fun z:ι→α=>(∀i,z i≠a) ∨ (∀i,z i≠b))=L∪R := by
    ext z; simp [L,R,Fintype.mem_piFinset]
  have intersection : L∩R=Fintype.piFinset (fun _ : ι=>({a,b}:Finset α)ᶜ) := by
    ext z
    simp only [L,R,mem_inter,Fintype.mem_piFinset,mem_compl,mem_singleton,mem_insert,not_or]
    exact forall_and.symm
  have c1 : L.card=(Fintype.card α-1)^(Fintype.card ι) := by simp [L,Fintype.card_piFinset,Finset.card_compl]
  have c2 : R.card=(Fintype.card α-1)^(Fintype.card ι) := by simp [R,Fintype.card_piFinset,Finset.card_compl]
  have c3 : (L∩R).card=(Fintype.card α-2)^(Fintype.card ι) := by rw [intersection];simp [Fintype.card_piFinset,Finset.card_compl,ab,Nat.sub_sub]
  have h:=Finset.card_union_add_card_inter L R
  have hi : ((L∪R).card:ℤ)+((L∩R).card:ℤ)=(L.card:ℤ)+(R.card:ℤ) := by exact_mod_cast h
  rw [c1,c2,c3] at hi
  push_cast at hi
  rw [un];linarith only [hi]

/-- Exact number of safe oriented lifts over the rational exceptional inert row. -/
theorem inert_safe_count {p:ℕ} [Fact p.Prime] (inert:p%4=3) (ι:Type*) [Fintype ι] [DecidableEq ι] :
    (((obstructed (p:=p) (fun _ : ι => (1:ZMod p)))ᶜ.card:ℤ)) =
    2*(p:ℤ)^(Fintype.card ι)-((p-1:ℕ):ℤ)^(Fintype.card ι) := by
  classical
  let a : Circle p 1 := ⟨(-1,0),by simp⟩
  let b : Circle p 1 := ⟨(1,0),by simp⟩
  have sep : a≠b := by
    intro eq
    have h:(-1:ZMod p)=1:=congrArg (fun z : Circle p 1 =>z.val.1) eq
    have two : (2:ZMod p)=0:=by linear_combination -h
    have div : p∣2:=(ZMod.natCast_eq_zero_iff 2 p).mp two
    have := Nat.le_of_dvd (by decide:0<2) div
    omega
  have eq : (obstructed (p:=p) (fun _ : ι=>(1:ZMod p)))ᶜ =
    univ.filter (fun z:ι→Circle p 1=>(∀i,z i≠a) ∨ (∀i,z i≠b)) := by
    ext z
    rw [mem_compl,obstructed_iff,mem_filter]
    simp only [mark inert,ite_true,Bool.false_eq_true,ite_false,mem_univ,true_and]
    have sa (i:ι) : (z i).val=(-1,0) ↔ z i=a := ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
    have sb (i:ι) : (z i).val=(1,0) ↔ z i=b := ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
    simp_rw [sa,sb]
    constructor
    · intro no; by_cases has:∃i,z i=a
      · obtain ⟨i,hi⟩:=has;exact Or.inr (fun j hj=>no ⟨i,j,hi,hj⟩)
      · exact Or.inl (fun i hi=>has ⟨i,hi⟩)
    · rintro (none|none) ⟨i,j,hi,hj⟩
      · exact none i hi
      · exact none j hj
  have formula:=finite_boxes (ι:=ι) a b sep
  rw [eq]
  convert formula using 1
  · congr 2; ext z; simp
  · rw [circle_size inert];simp

end
end Sun28.CommonRows
#print axioms Sun28.CommonRows.inert_safe_count