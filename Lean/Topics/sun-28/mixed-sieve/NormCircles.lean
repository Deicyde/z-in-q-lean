import ContactLocalSieve
import Mathlib.FieldTheory.Finite.Basic

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

namespace Sun28.MixedSieve
open Sun28.NormSieve
variable {p : ℕ} [Fact p.Prime]
abbrev F (p : ℕ) := ZMod p

/-- Gaussian residues with prescribed norm. -/
abbrev Circle (p : ℕ) (t : ZMod p) := {z : ZMod p × ZMod p // z.1^2+z.2^2=t}


abbrev parameters (p : ℕ) [Fact p.Prime] := {s : ZMod p // 1+s^2≠0}


/-- The pencil of lines through (-1,0) on the circle. -/
noncomputable def parametrization (odd : p≠2) : Option (parameters p) ≃ Circle p 1 := by
  classical
  have two : (2:F p)≠0 := by
    rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
    exact fun d => odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp d)
  let point (s : parameters p) : Circle p 1 :=
    ⟨((1-s.val^2)/(1+s.val^2),2*s.val/(1+s.val^2)),by
      dsimp
      field_simp [s.property] <;> ring⟩
  let slope (z : Circle p 1) (h : 1+z.val.1≠0) : parameters p :=
    ⟨z.val.2/(1+z.val.1),by
      intro eq
      have rel:=z.property
      field_simp [h] at eq
      apply h
      apply (mul_eq_zero.mp (show (2:F p)*(1+z.val.1)=0 by linear_combination eq-rel)).resolve_left two⟩
  refine ⟨(fun s => match s with | none => ⟨(-1,0),by simp⟩ | some r => point r),
     (fun z => if h : 1+z.val.1=0 then none else some (slope z h)),?_,?_⟩
  · rintro (_|s)
    · simp
    · have hx : 1+(point s).val.1≠0 := by
        dsimp [point]
        intro e
        field_simp [s.property] at e
        apply two
        linear_combination e
      simp only [hx,reduceDIte,Option.some.injEq]
      apply Subtype.ext
      change (2*s.val/(1+s.val^2))/(1+(point s).val.1) = s.val
      apply (div_eq_iff hx).mpr
      dsimp [point]
      field_simp [s.property] <;> ring
  · intro z
    rcases z with ⟨⟨x,y⟩,hxy⟩
    change x^2+y^2=1 at hxy
    dsimp only
    by_cases hx : 1+x=0
    · simp only [hx,reduceDIte]

      change 1+x=0 at hx
      have eq : x= -1 := by linear_combination hx
      subst x
      have ys : y^2=0 := by linear_combination hxy
      have yz := (pow_eq_zero_iff (by decide : 2≠0)).mp ys
      subst y
      rfl
    · simp only [hx,reduceDIte]
      apply Subtype.ext
      have denom := (slope ⟨(x,y),hxy⟩ hx).property
      change 1+(y/(1+x))^2≠0 at denom
      apply Prod.ext
      · dsimp [point,slope]
        apply (div_eq_iff denom).mpr
        field_simp [hx]
        <;> linear_combination -(1+x)*hxy
      · dsimp [point,slope]
        apply (div_eq_iff denom).mpr
        field_simp [hx]
        <;> linear_combination -y*hxy

/-- Multiplication by a point of norm t identifies every nonzero fibre with the unit circle. -/
noncomputable def rotate {t : F p} (ht : t≠0) : Circle p 1 ≃ Circle p t := by
  classical
  let a : F p := (ZMod.sq_add_sq p t).choose
  let b : F p := (ZMod.sq_add_sq p t).choose_spec.choose
  have hab : a^2+b^2=t := (ZMod.sq_add_sq p t).choose_spec.choose_spec
  refine ⟨fun z => ⟨(a*z.val.1-b*z.val.2,b*z.val.1+a*z.val.2),?_⟩,
    fun z => ⟨((a*z.val.1+b*z.val.2)/t,(a*z.val.2-b*z.val.1)/t),?_⟩,?_,?_⟩
  · dsimp
    linear_combination (z.val.1^2+z.val.2^2)*hab+t*z.property
  · dsimp
    field_simp [ht]
    <;> linear_combination (z.val.1^2+z.val.2^2)*hab+t*z.property
  · intro z
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp [ht]
    · linear_combination z.val.1*hab
    · linear_combination z.val.2*hab
  · intro z
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp [ht]
    · linear_combination z.val.1*hab
    · linear_combination z.val.2*hab

/-- Exact order of every nonzero norm fibre at an odd prime. -/
theorem circle_card (odd : p≠2) {t : F p} (ht : t≠0) :
    (Fintype.card (Circle p t) : ℤ) = (p:ℤ) - legendreSym p (-1) := by
  classical
  have count := legendreSym.card_sqrts (p:=p) odd (-1)
  simp only [Int.cast_neg,Int.cast_one,Set.toFinset_card] at count
  have small : Fintype.card {s : F p // 1+s^2=0} ≤ p := by
    simpa only [ZMod.card] using Fintype.card_le_of_injective
      (fun s : {s : F p // 1+s^2=0} => s.val) Subtype.val_injective
  have card := Fintype.card_congr ((parametrization odd).trans (rotate ht))
  change Fintype.card (Option {s : F p // ¬ (fun s : F p => 1+s^2=0) s}) = _ at card
  rw [Fintype.card_option,Fintype.card_subtype_compl,ZMod.card] at card
  change Fintype.card {s : F p // (fun s : F p => 1+s^2=0) s} ≤ p at small
  have same : Fintype.card {s : F p // 1+s^2=0} = Fintype.card {s : F p // s^2= -1} :=
    Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun s => by
      change 1+s^2=0 ↔ s^2= -1
      constructor <;> intro h <;> linear_combination h)
  change (Fintype.card {s : F p // s^2= -1} : ℤ)=legendreSym p (-1)+1 at count
  have d : (↑(p-Fintype.card {s : F p // 1+s^2=0}):ℤ)=(p:ℤ)-(Fintype.card {s : F p // 1+s^2=0}:ℤ) :=
    Int.natCast_sub small
  rw [←card,Nat.cast_add,Nat.cast_one,d]
  rw [same]
  linarith

theorem circle_card_lower (odd : p≠2) {t : F p} (ht : t≠0) :
    p-1 ≤ Fintype.card (Circle p t) := by
  have e := circle_card odd ht
  have sign := legendreSym.sq_one (p:=p) (a:=(-1:ℤ)) (by simp)
  have bound : legendreSym p (-1) ≤ 1 := by nlinarith [sq_nonneg (legendreSym p (-1)-1)]
  omega

end Sun28.MixedSieve
#print axioms Sun28.MixedSieve.parametrization
#print axioms Sun28.MixedSieve.rotate
#print axioms Sun28.MixedSieve.circle_card
#print axioms Sun28.MixedSieve.circle_card_lower
