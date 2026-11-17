import TailCounts

namespace Sun28.SieveTail
open ManuscriptV15.Arithmetic Sun28.ContactFactors Sun28.WeightedSelection
noncomputable section

variable {A : Fin 3 → ℚ} {d : ℕ} {H Y : ℝ}

def horizontal (flip : Bool) (g h : Gaussian) : ℤ :=
  if flip then zcoord g h else xcoord g h
def vertical (flip : Bool) (g h : Gaussian) : ℤ :=
  if flip then xcoord g h else zcoord g h

def pairRecords (boxes : CountingBoxes A d H Y) (N V R : ℕ) (i j : ↥(shifts A)) :
    Finset (Candidate A d H Y) := by
  classical exact (boxes.records N).filter fun a => a.v=V ∧ ∃ p : ℕ, p.Prime ∧ R<p ∧
    p∣adjacentNorm (a.gaussian i) true ∧ p∣adjacentNorm (a.gaussian j) false

def recordSlice (boxes : CountingBoxes A d H Y) (N V : ℕ) (i j : ↥(shifts A))
    (t : ℤ) (g p : ℕ) (flip : Bool) : Finset (Candidate A d H Y) := by
  classical exact (boxes.records N).filter fun a =>
    a.v=V ∧ tcoord (a.gaussian i) (a.gaussian j)=t ∧
      (Int.gcd (t.natAbs:ℤ) (horizontal flip (a.gaussian i) (a.gaussian j)) = g) ∧
      (p:ℤ) ∣ t^2+(horizontal flip (a.gaussian i) (a.gaussian j))^2

def sliceBound (B g q p : ℕ) : ℚ :=
  let L := 2*(B:ℚ)+1
  (if p∣g then L/g+1 else 2*(L/(g*p)+1))*(L/q+1)

def signedCoordinate (neg : Bool) (g q : ℕ) : ℤ :=
  if neg then -((g*q:ℕ):ℤ) else ((g*q:ℕ):ℤ)

def chartBox (boxes : CountingBoxes A d H Y) (N V B : ℕ) (i j : ↥(shifts A)) : Prop :=
  ∀ a∈boxes.records N,a.v=V →
    (tcoord (a.gaussian i) (a.gaussian j)).natAbs≤B ∧
    xcoord (a.gaussian i) (a.gaussian j)∈interval B ∧
    zcoord (a.gaussian i) (a.gaussian j)∈interval B

theorem record_slice_bound (boxes : CountingBoxes A d H Y) (N V B : ℕ) (i j : ↥(shifts A))
    (bounds : chartBox boxes N V B i j)
    (t : ℤ) (g q p : ℕ) [Fact p.Prime] (gp : 0 < g) (qp : 0 < q)
    (abs_t : t.natAbs=g*q) (flip : Bool) :
    ((recordSlice boxes N V i j t g p flip).card:ℚ) ≤ sliceBound B g q p := by
  classical
  let S := recordSlice boxes N V i j t g p flip
  let f : Candidate A d H Y → ℤ×ℤ := fun r =>
    (horizontal flip (r.gaussian i) (r.gaussian j),vertical flip (r.gaussian i) (r.gaussian j))
  let M := S.image f
  have detail (a : Candidate A d H Y) (ha : a∈S) := (Finset.mem_filter.mp ha)
  have inject : Set.InjOn f S := by
    intro a ha b hb ef
    obtain ⟨sa,va,ta,_,_⟩ := detail a ha
    obtain ⟨sb,vb,tb,_,_⟩ := detail b hb
    apply chart_injective boxes N i j sa sb (va.trans vb.symm) (ta.trans tb.symm)
    · cases flip
      · exact congrArg Prod.fst ef
      · exact congrArg Prod.snd ef
    · cases flip
      · exact congrArg Prod.snd ef
      · exact congrArg Prod.fst ef
  change (S.card:ℚ) ≤ _
  rw [←Finset.card_image_of_injOn inject]
  apply fixed_slice B g q gp qp (gap i j*(V:ℤ)^2) M
  · intro m h
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
    obtain ⟨sa,va,_,_,_⟩:=detail a ha
    have data := (bounds a sa va).2
    cases flip
    · exact data
    · exact ⟨data.2,data.1⟩
  · intro m h
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
    rw [←abs_t]
    exact (detail a ha).2.2.2.1
  · intro m h
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
    obtain ⟨_,va,ta,_,_⟩:=detail a ha
    have eq := hyperbolic a i j
    dsimp only at eq
    rw [va,ta] at eq
    rw [←abs_t]
    apply Int.natAbs_dvd.mpr
    have k : t ∣ gap i j*(V:ℤ)^2-xcoord (a.gaussian i) (a.gaussian j)*zcoord (a.gaussian i) (a.gaussian j) :=
      ⟨_,eq.symm⟩
    cases flip
    · exact k
    · simpa only [f,horizontal,vertical,ite_true,mul_comm (zcoord _ _) (xcoord _ _)] using k
  · intro m h
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
    rw [←abs_t,Int.natCast_natAbs, sq_abs]
    exact (detail a ha).2.2.2.2

private theorem cover_bound {α ι : Type*} [DecidableEq α] (S : Finset α) (T : Finset ι)
    (F : ι→Finset α) (f : ι→ℚ)
    (into : ∀ a∈S,∃ i∈T,a∈F i) (size : ∀ i∈T,((F i).card:ℚ)≤f i) :
    (S.card:ℚ)≤∑ i∈T,f i := by
  classical
  have h : S ⊆ T.biUnion F := fun _ ha => Finset.mem_biUnion.mpr (into _ ha)
  calc (S.card:ℚ) ≤ ((T.biUnion F).card:ℚ) := by exact_mod_cast Finset.card_le_card h
       _ ≤ ∑ i∈T,((F i).card:ℚ) := by exact_mod_cast Finset.card_biUnion_le (s:=T) (t:=F)
       _ ≤ _ := Finset.sum_le_sum size

/-- Finite upper bound on the original candidate records, for one denominator
parameter v and one ordered pair i≠j. The four nested finite sums enumerate
only actual divisors of K=κv² and of K+2t. -/
theorem fixed_v_candidate_bound (boxes : CountingBoxes A d H Y) (N V B R : ℕ)
    (i j : ↥(shifts A)) (ij : i≠j) (bounds : chartBox boxes N V B i j) :
    let K := gap i j*(V:ℤ)^2
    ((pairRecords boxes N V R i j).card:ℚ) ≤
      ∑ g∈K.natAbs.divisors, ∑ q∈Finset.Icc 1 (B/g), ∑ e : Bool,
        ∑ p∈(K+2*signedCoordinate e g q).natAbs.primeFactors.filter (fun p => R<p),
          2*sliceBound B g q p := by
  classical
  let K := gap i j*(V:ℤ)^2
  let P (g q : ℕ) (e : Bool) := (K+2*signedCoordinate e g q).natAbs.primeFactors.filter (fun p => R<p)
  let S (g q : ℕ) (e : Bool) (p : ℕ) (flip : Bool) :=
    recordSlice boxes N V i j (signedCoordinate e g q) g p flip
  let C (g q : ℕ) (e : Bool) (p : ℕ) := Finset.univ.biUnion (S g q e p)
  let D (g q : ℕ) (e : Bool) := (P g q e).biUnion (C g q e)
  let E (g q : ℕ) := Finset.univ.biUnion (D g q)
  let F (g : ℕ) := (Finset.Icc 1 (B/g)).biUnion (E g)
  dsimp only
  apply cover_bound _ K.natAbs.divisors F _ ?_ ?_
  · intro a ha
    obtain ⟨rec,va,p,prime,large,plus,minus⟩:=Finset.mem_filter.mp ha
    let _ : Fact p.Prime := ⟨prime⟩
    let t := tcoord (a.gaussian i) (a.gaussian j)
    obtain ⟨tn,kn,pf,X,Z,either,form,_,factor,_⟩:=candidate_chart a i j ij plus minus
    change p∈(gap i j*(a.v:ℤ)^2+2*t).natAbs.primeFactors at pf
    rw [va] at pf kn factor
    let g := Int.gcd (t.natAbs:ℤ) X
    let q := t.natAbs/g
    have gp : 0 < g := Int.gcd_pos_of_ne_zero_left _ (by exact_mod_cast Int.natAbs_ne_zero.mpr tn)
    have dg : g∣t.natAbs := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_left _ _)
    have extend : g*q=t.natAbs := Nat.mul_div_cancel' dg
    have pos : 0 < g*q := extend ▸ Int.natAbs_pos.mpr tn
    have qp : 0 < q := Nat.pos_of_ne_zero (fun h => by simp [h] at pos)
    have qB : q≤B/g := Nat.le_div_iff_mul_le gp |>.mpr (by rw [mul_comm,extend]; exact (bounds a rec va).1)
    have sign : ∃ e : Bool, signedCoordinate e g q=t := by
      by_cases ht : 0≤t
      · exact ⟨false,by simp only [signedCoordinate,ite_false,Bool.false_eq_true,extend,Int.natAbs_of_nonneg ht]⟩
      · refine ⟨true,?_⟩
        simp only [signedCoordinate,ite_true,extend,Int.natCast_natAbs,abs_of_neg (lt_of_not_ge ht),neg_neg]
    obtain ⟨e,se⟩:=sign
    refine ⟨g,Nat.mem_divisors.mpr ⟨factor,Int.natAbs_ne_zero.mpr kn⟩,
      Finset.mem_biUnion.mpr ⟨q,Finset.mem_Icc.mpr ⟨qp,qB⟩,Finset.mem_biUnion.mpr
       ⟨e,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨p,?_,Finset.mem_biUnion.mpr ?_⟩⟩⟩⟩
    · exact Finset.mem_filter.mpr ⟨by simpa only [se,K] using pf,large⟩
    · rcases either with ⟨xx,_⟩|⟨xx,_⟩
      · refine ⟨false,Finset.mem_univ _,Finset.mem_filter.mpr ⟨rec,va,se.symm,?_,?_⟩⟩
        · simp only [se,horizontal,Bool.false_eq_true,ite_false,←xx]; rfl
        · simpa only [se,horizontal,Bool.false_eq_true,ite_false,←xx] using form
      · refine ⟨true,Finset.mem_univ _,Finset.mem_filter.mpr ⟨rec,va,se.symm,?_,?_⟩⟩
        · simp only [se,horizontal,ite_true,←xx]; rfl
        · simpa only [se,horizontal,ite_true,←xx] using form
  · intro g hg
    have gp := Nat.pos_of_mem_divisors hg
    apply cover_bound _ _ (E g) _ (fun _ h => Finset.mem_biUnion.mp h)
    intro q hq
    have qp : 0<q := (Finset.mem_Icc.mp hq).1
    apply cover_bound _ _ (D g q) _ (fun _ h => Finset.mem_biUnion.mp h)
    intro e _
    apply cover_bound _ _ (C g q e) _ (fun _ h => Finset.mem_biUnion.mp h)
    intro p hp
    let _ : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1⟩
    have abs_t : (signedCoordinate e g q).natAbs=g*q := by cases e <;> simp only [signedCoordinate,ite_true,Bool.false_eq_true,ite_false,Int.natAbs_neg,Int.natAbs_natCast]
    have comp := cover_bound (C g q e p) Finset.univ (S g q e p) (fun _ => sliceBound B g q p)
        (fun _ h => Finset.mem_biUnion.mp h) (fun flip _ =>
          record_slice_bound boxes N V B i j bounds _ g q p gp qp abs_t flip)
    simpa [two_mul] using comp

end
end Sun28.SieveTail
#print axioms Sun28.SieveTail.record_slice_bound
#print axioms Sun28.SieveTail.fixed_v_candidate_bound
