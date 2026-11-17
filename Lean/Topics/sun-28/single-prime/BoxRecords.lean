import AnalyticInputs

namespace Sun28.SinglePrime
open Sun28.WeightedSelection Sun28.ContactFactors
noncomputable section

variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

abbrev Record (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) := Candidate A d H Y

def pair (a : Record A d H Y) : ℕ×ℕ := (a.u,a.v)

def eligible (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (q : ℕ×ℕ) : Prop :=
  ∃ a : Record A d H Y,pair a=q

noncomputable def representative (q : {q // eligible A d H Y q}) : Record A d H Y := q.property.choose

theorem pair_representative (q : {q // eligible A d H Y q}) : pair (representative q)=q.val :=
  q.property.choose_spec

/-- Equal numerical pairs give the same prime values on the shift set and hence the same weight. -/
theorem weight_eq_of_pair {a b : Record A d H Y} (eq : pair a=pair b) : weight a=weight b := by
  apply Finset.prod_congr rfl
  intro r _
  have t := congrArg (fun q : ℕ×ℕ => (q.1:ℤ)+offset (dilation A) r.val*(q.2:ℤ)^2) eq
  have h := (a.values.equation r.val r.property).trans (t.trans (b.values.equation r.val r.property).symm)
  exact congrArg (fun n : ℕ => Real.log (n:ℝ)) (Int.ofNat_inj.mp h)

open scoped Classical in
def pairs (b t : ℕ) : Finset {q // eligible A d H Y q} :=
  (((Finset.Ioc (b/2) b) ×ˢ (Finset.Icc 1 t)).subtype (eligible A d H Y))

def box (b t : ℕ) : Finset (Record A d H Y) := by
  classical exact (pairs b t).image representative

theorem box_mem {a : Record A d H Y} {b t : ℕ} (ha : a∈box b t) :
    b<2*a.u ∧ a.u≤b ∧ a.v≤t := by
  classical
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
  have x := pair_representative q
  have hu := congrArg Prod.fst x
  have hv := congrArg Prod.snd x
  have h : q.val ∈ ((Finset.Ioc (b/2) b) ×ˢ (Finset.Icc 1 t)) := by simpa [pairs] using hq
  have u := Finset.mem_Ioc.mp (Finset.mem_product.mp h).1
  have v := Finset.mem_Icc.mp (Finset.mem_product.mp h).2
  change (representative q).u=q.val.1 at hu
  change (representative q).v=q.val.2 at hv
  omega

theorem box_unique {a a' : Record A d H Y} {b t : ℕ} (ha : a∈box b t) (hb : a'∈box b t)
    (u : a.u=a'.u) (v : a.v=a'.v) : a=a' := by
  classical
  obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp ha
  obtain ⟨r,_,rfl⟩:=Finset.mem_image.mp hb
  have e : pair (representative q)=pair (representative r) := Prod.ext u v
  rw [pair_representative,pair_representative] at e
  exact congrArg representative (Subtype.ext e)

theorem box_covers (a : Record A d H Y) {b t : ℕ}
    (low : b<2*a.u) (high : a.u≤b) (width : a.v≤t) :
    ∃ a' : Record A d H Y,a'∈box b t ∧ pair a'=pair a := by
  classical
  let q : {q // eligible A d H Y q} := ⟨pair a,a,rfl⟩
  refine ⟨representative q,Finset.mem_image.mpr ⟨q,?_,rfl⟩,pair_representative q⟩
  have pos:=a.positive
  have h : pair a∈((Finset.Ioc (b/2) b) ×ˢ (Finset.Icc 1 t)) :=
    Finset.mem_product.mpr ⟨Finset.mem_Ioc.mpr ⟨by change b/2<a.u; omega,high⟩,
      Finset.mem_Icc.mpr ⟨pos,width⟩⟩
  simpa [q,pairs] using h

/-- One global choice of Gaussian generators per numerical pair works in every rectangle. -/
def numericalBoxes (width : ℕ→ℕ)
    (grows : ∀ m : ℕ,∃ b₀ : ℕ,∀ b : ℕ,b₀≤b → m≤width b)
    (short : ∀ ε : ℝ,0<ε → ∃ b₀ : ℕ,∀ b : ℕ,b₀≤b → (width b:ℝ)^2≤ε*b) :
    CountingBoxes A d H Y where
  width := width
  grows := grows
  short := short
  records b := box b (width b)
  inBox _ _ h := box_mem h
  uniquePair _ _ ha _ hb := box_unique ha hb
  covers _ a low high w := by
    obtain ⟨a',mem,eq⟩:=box_covers a low high w
    exact ⟨a',mem,congrArg Prod.fst eq,congrArg Prod.snd eq⟩

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.weight_eq_of_pair
#print axioms Sun28.SinglePrime.box_mem
#print axioms Sun28.SinglePrime.box_unique
#print axioms Sun28.SinglePrime.box_covers
#print axioms Sun28.SinglePrime.numericalBoxes
