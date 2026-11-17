import PrimitiveFibre
import Mathlib.Data.Int.CardIntervalMod

namespace Sun28.SieveTail
open ManuscriptV15.Arithmetic Sun28.ContactFactors Sun28.WeightedSelection

/-- Every residue class has at most one more element in an interval than
its length divided by the modulus, uniformly in the position of the interval. -/
theorem interval_class (a b r v : ℤ) (ab : a ≤ b) (pr : 0 < r) :
    (((Finset.Ico a b).filter (fun n => n ≡ v [ZMOD r])).card:ℚ) ≤
      ((b:ℚ)-a)/r+1 := by
  have e := Int.Ico_filter_modEq_card a b pr v
  have rpos : 0 < (r:ℚ) := by exact_mod_cast pr
  have nonneg : 0 ≤ ((b:ℚ)-a)/r := div_nonneg (sub_nonneg.mpr (by exact_mod_cast ab)) rpos.le
  rw [←Int.cast_natCast, e]
  by_cases ord : ⌈((a:ℚ)-v)/r⌉ ≤ ⌈((b:ℚ)-v)/r⌉
  · rw [max_eq_left (sub_nonneg.mpr ord),Int.cast_sub]
    have h₁ := Int.ceil_lt_add_one (((b:ℚ)-v)/r)
    have h₂ := Int.le_ceil (((a:ℚ)-v)/r)
    rw [show ((b:ℚ)-a)/r = ((b:ℚ)-v)/r-((a:ℚ)-v)/r by ring]
    linarith
  · rw [max_eq_right (by omega),Int.cast_zero]
    linarith

def interval (B : ℕ) : Finset ℤ := Finset.Ico (-(B:ℤ)) ((B:ℤ)+1)

/-- Counting in the signed box -B,...,B. -/
theorem one_class (B r : ℕ) (rpos : 0<r) (S : Finset ℤ)
    (bound : S⊆interval B)
    (same : ∀ x∈S,∀ y∈S,x ≡ y [ZMOD (r:ℤ)]) :
    (S.card:ℚ) ≤ (2*(B:ℚ)+1)/r+1 := by
  by_cases empty : S.Nonempty
  · obtain ⟨v,hv⟩:=empty
    have incl : S ⊆ (interval B).filter (fun x => x ≡ v [ZMOD (r:ℤ)]) :=
      fun x hx => Finset.mem_filter.mpr ⟨bound hx,same x hx v hv⟩
    have h := interval_class (-(B:ℤ)) ((B:ℤ)+1) (r:ℤ) v (by omega) (by exact_mod_cast rpos)
    push_cast at h
    calc (S.card:ℚ) ≤ (((interval B).filter (fun n => n ≡ v [ZMOD (r:ℤ)])).card:ℚ) := by
             exact_mod_cast Finset.card_le_card incl
         _ ≤ _ := by simpa only [interval,show (B:ℚ)+1-(-(B:ℚ))=2*(B:ℚ)+1 by ring] using h
  · rw [Finset.not_nonempty_iff_eq_empty.mp empty]
    simp
    positivity

theorem fibre_bound {α β : Type*} [DecidableEq β] (S : Finset α) (T : Finset β) (f : α→β)
    (into : (S:Set α).MapsTo f T) (C : ℚ)
    (per : ∀ t∈T,((S.filter (fun s => f s=t)).card:ℚ) ≤ C) :
    (S.card:ℚ) ≤ T.card*C := by
  rw [Finset.card_eq_sum_card_fiberwise into,Nat.cast_sum]
  exact (Finset.sum_le_sum per).trans (by simp)

/-- Counts *undivided* coordinates by residue classes with modulus g*p (or g
in the exceptional case p|g). Thus the +1 in this bound is kept even for a
prime larger than the original box width. -/
theorem horizontal_count {p : ℕ} [Fact p.Prime] (B g : ℕ) (gp : 0 < g) (U : ℤ)
    (S : Finset ℤ) (bound : S⊆interval B) (multiples : ∀ x∈S,(g:ℤ) ∣ x)
    (root : ∀ x∈S, (p:ℤ) ∣ ((g:ℤ)*U)^2+x^2) :
    (S.card:ℚ) ≤ if p∣g then (2*(B:ℚ)+1)/g+1 else 2*((2*(B:ℚ)+1)/(g*p)+1) := by
  classical
  split_ifs with pg
  · apply one_class B g gp S bound
    intro x hx y hy
    exact Int.modEq_iff_dvd.mpr (dvd_sub (multiples y hy) (multiples x hx))
  · let f : ℤ → ZMod p := fun x => ((x/(g:ℤ):ℤ):ZMod p)
    let roots := Finset.univ.filter (fun X : ZMod p => X^2= -(U:ZMod p)^2)
    have maps : (S:Set ℤ).MapsTo f roots := by
      intro x hx
      have hx' := Int.ediv_mul_cancel (multiples x hx)
      have data : (p:ℤ) ∣ (U*(g:ℤ))^2+(x/(g:ℤ)*(g:ℤ))^2 := by
        rw [hx',mul_comm U]; exact root x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(primitive_root data (rfl : U*(g:ℤ)=_)).resolve_left
        fun q => pg (Int.natCast_dvd_natCast.mp q.1)⟩
    let C : ℚ := (2*(B:ℚ)+1)/((g:ℚ)*p)+1
    apply (fibre_bound S roots f maps C ?_).trans
    · have hnat : roots.card ≤ 2 := roots_card (U:ZMod p)
      have card : (roots.card:ℚ) ≤ 2 := by exact_mod_cast hnat
      exact mul_le_mul_of_nonneg_right card (by dsimp [C]; positivity)
    · intro v _
      let F := S.filter (fun x => f x=v)
      have inc : F⊆interval B := fun x hx => bound ((Finset.mem_filter.mp hx).1)
      have h := one_class B (g*p) (Nat.mul_pos gp (Fact.out : p.Prime).pos) F inc (by
        intro x hx y hy
        obtain ⟨sx,ex⟩ := Finset.mem_filter.mp hx
        obtain ⟨sy,ey⟩ := Finset.mem_filter.mp hy
        have eq := (ZMod.intCast_eq_intCast_iff (x/(g:ℤ)) (y/(g:ℤ)) p).mp (ex.trans ey.symm)
        have both := eq.mul_right' (c := (g:ℤ))
        rw [Int.ediv_mul_cancel (multiples x sx),Int.ediv_mul_cancel (multiples y sy)] at both
        simpa only [Nat.cast_mul,mul_comm (p:ℤ) (g:ℤ)] using both)
      simpa only [Nat.cast_mul] using h

/-- Bound for a fixed absolute chart coordinate m=gq, fixed first-coordinate
gcd g, and fixed prime. The first projection only carries the two possible
reduced roots. Its fibres carry one complementary congruence class. -/
theorem fixed_slice {p : ℕ} [Fact p.Prime] (B g q : ℕ) (gp : 0 < g) (qp : 0 < q)
    (K : ℤ) (S : Finset (ℤ×ℤ))
    (inBox : ∀ a∈S,a.1∈interval B ∧ a.2∈interval B)
    (common : ∀ a∈S, Int.gcd ((g*q:ℕ):ℤ) a.1=g)
    (hyper : ∀ a∈S, ((g*q:ℕ):ℤ) ∣ K-a.1*a.2)
    (form : ∀ a∈S,(p:ℤ) ∣ ((g*q:ℕ):ℤ)^2+a.1^2) :
    let L := 2*(B:ℚ)+1
    (S.card:ℚ) ≤ (if p∣g then L/g+1 else 2*(L/(g*p)+1))*(L/q+1) := by
  classical
  dsimp only
  let T := S.image Prod.fst
  have hb : T⊆interval B := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact (inBox a ha).1
  have hd (x : ℤ) (hx : x∈T) : (g:ℤ) ∣ x := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [←common a ha]
    exact Int.gcd_dvd_right _ _
  have hf (x : ℤ) (hx : x∈T) : (p:ℤ) ∣ ((g:ℤ)*(q:ℤ))^2+x^2 := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    simpa only [Nat.cast_mul] using form a ha
  have horizontal := horizontal_count B g gp (q:ℤ) T hb hd hf
  apply (fibre_bound S T Prod.fst (fun _ h => Finset.mem_image_of_mem _ h) ((2*(B:ℚ)+1)/q+1) ?_).trans
  · exact mul_le_mul_of_nonneg_right horizontal (by positivity)
  · intro x _
    let F := S.filter (fun a => a.1=x)
    let V := F.image Prod.snd
    have card : V.card=F.card := Finset.card_image_of_injOn (by
      intro a ha b hb eq
      exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) eq)
    rw [←show V.card=(S.filter (fun a => a.1=x)).card from card]
    apply one_class B q qp V
    · intro z hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      exact (inBox a (Finset.mem_filter.mp ha).1).2
    · intro z hz w hw
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨sa,ea⟩ := Finset.mem_filter.mp ha
      obtain ⟨sb,eb⟩ := Finset.mem_filter.mp hb
      have eq := ea.trans eb.symm
      have rel := (primitive_fibre (Nat.mul_pos gp qp) (hyper a sa)).2.2 b.2 (eq ▸ hyper b sb)
      rw [common a sa,Nat.cast_mul,Int.mul_ediv_cancel_left _ (by exact_mod_cast gp.ne')] at rel
      exact rel

end Sun28.SieveTail
#print axioms Sun28.SieveTail.interval_class
#print axioms Sun28.SieveTail.one_class
#print axioms Sun28.SieveTail.fibre_bound
#print axioms Sun28.SieveTail.horizontal_count
#print axioms Sun28.SieveTail.fixed_slice
