import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic

/-! The two ordinary anchors of Sun's certificate and its Lucas polynomial. -/
namespace Sun28.Ordinary
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))

theorem integral_int (a : ℤ) : 0 ≤ v (a:K) := by
  have natIntegral (n : ℕ) : 0 ≤ v (n:K) := by
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact v.map_le_add ih (le_of_eq v.map_one.symm)
  cases a with
  | ofNat n => simpa using natIntegral n
  | negSucc n =>
    have e : ((Int.negSucc n:ℤ):K) = -((n+1:ℕ):K) := by simp only [Int.cast_negSucc, Nat.cast_succ]
    rw [e,v.map_neg]
    exact natIntegral (n+1)

private theorem integral_times {k : WithTop ℤ} {a b : K} (ha : 0 ≤ v a) (hb : k ≤ v b) :
    k ≤ v (a*b) := by
  rw [v.map_mul]
  simpa only [zero_add] using add_le_add ha hb

/-- Subtract the two denominator-cleared approximations. The anchor c is a unit. -/
theorem two_anchor_congruence {r : WithTop ℤ} {h c m n : ℤ} {L L' : K}
    (hc : v (c:K)=0)
    (first : r ≤ v ((h:K)*L-(m:K)))
    (second : r ≤ v (((h-c:ℤ):K)*L'-((m-c*n:ℤ):K)))
    (contact : r ≤ v (L-L')) : r ≤ v (L-(n:K)) := by
  have step := v.map_le_sub (v.map_le_sub first second)
    (integral_times v (integral_int v (h-c)) contact)
  have eqn : ((h:K)*L-(m:K))-(((h-c:ℤ):K)*L'-((m-c*n:ℤ):K))-
      ((h-c:ℤ):K)*(L-L') = (c:K)*(L-(n:K)) := by push_cast; ring
  rw [eqn,v.map_mul,hc,zero_add] at step
  exact step

/-- Congruence to an integer, with an additive valuation that allows v(0)=∞. -/
def Near (r : ℕ) (a : K) (n : ℤ) : Prop := (r:WithTop ℤ) ≤ v (a-(n:K))

theorem Near.integral {r : ℕ} {a : K} {n : ℤ} (h : Near v r a n) : 0 ≤ v a := by
  have hr : (0:WithTop ℤ) ≤ r := by exact_mod_cast (Nat.zero_le r)
  have hv := v.map_le_add (hr.trans h) (integral_int v n)
  simpa using hv

theorem Near.sub {r : ℕ} {a b : K} {n m : ℤ} (ha : Near v r a n) (hb : Near v r b m) :
    Near v r (a-b) (n-m) := by
  have h := v.map_le_sub (show (r:WithTop ℤ) ≤ v (a-(n:K)) from ha)
    (show (r:WithTop ℤ) ≤ v (b-(m:K)) from hb)
  unfold Near
  rw [show a-b-((n-m:ℤ):K)=(a-(n:K))-(b-(m:K)) by push_cast; ring]
  exact h

theorem Near.add {r : ℕ} {a b : K} {n m : ℤ} (ha : Near v r a n) (hb : Near v r b m) :
    Near v r (a+b) (n+m) := by
  have h := v.map_le_add (show (r:WithTop ℤ) ≤ v (a-(n:K)) from ha)
    (show (r:WithTop ℤ) ≤ v (b-(m:K)) from hb)
  unfold Near
  rw [show a+b-((n+m:ℤ):K)=(a-(n:K))+(b-(m:K)) by push_cast; ring]
  exact h

theorem Near.mul {r : ℕ} {a b : K} {n m : ℤ} (ha : Near v r a n) (hb : Near v r b m) :
    Near v r (a*b) (n*m) := by
  have term₁ := integral_times v (ha.integral v) (show (r:WithTop ℤ) ≤ v (b-(m:K)) from hb)
  have term₂ := integral_times v (integral_int v m) (show (r:WithTop ℤ) ≤ v (a-(n:K)) from ha)
  have identity : a*b-((n*m:ℤ):K) = a*(b-(m:K))+(m:K)*(a-(n:K)) := by push_cast; ring
  unfold Near
  rw [identity]
  exact v.map_le_add term₁ term₂

/-- Sun's ordinary polynomial does not involve the first coordinate n. -/
def lucas {R : Type*} [Ring R] (s t z : R) := t^2-s*(s-2)*t*z+(s-2)^2*z^2-1

theorem lucas_congruence {r : ℕ} {a b c : K} {s t z : ℤ}
    (hs : Near v r a s) (ht : Near v r b t) (hz : Near v r c z) :
    Near v r (lucas a b c) (lucas s t z) := by
  have one : Near v r (1:K) 1 := by simp [Near]
  have two : Near v r (2:K) 2 := by simp [Near]
  have sub := hs.sub v two
  have ans := (((ht.mul v ht).sub v (((hs.mul v sub).mul v ht).mul v hz)).add v
    (((sub.mul v sub).mul v (hz.mul v hz)))).sub v one
  simpa only [lucas,pow_two] using ans

/-- The last six of Sun's sixteen tests give both output precisions
as soon as the two denominator-cleared log approximations are available. -/
theorem ordinary_precisions {c h : ℤ} {n m : Fin 4 → ℤ} {L L' : Fin 4 → K} {β : K}
    (hc : v (c:K)=0)
    (first : ∀ i, (64:WithTop ℤ) ≤ v ((h:K)*L i-(m i:K)))
    (second : ∀ i, (64:WithTop ℤ) ≤ v (((h-c:ℤ):K)*L' i-((m i-c*n i:ℤ):K)))
    (contacts : ∀ i, (64:WithTop ℤ) ≤ v (L i-L' i))
    (testΔ : (64:WithTop ℤ) ≤ v (lucas (L 1) (L 2) (L 3)))
    (testβ : (16:WithTop ℤ) ≤ v (L 0-β)) :
    (64:WithTop ℤ) ≤ v ((lucas (n 1) (n 2) (n 3):ℤ):K) ∧
      (16:WithTop ℤ) ≤ v (β-(n 0:K)) := by
  have near (i : Fin 4) : Near v 64 (L i) (n i) :=
    two_anchor_congruence v hc (first i) (second i) (contacts i)
  have D := lucas_congruence v (near 1) (near 2) (near 3)
  have d := v.map_le_sub testΔ (show (64:WithTop ℤ) ≤ v (lucas (L 1) (L 2) (L 3)-
    ((lucas (n 1) (n 2) (n 3):ℤ):K)) from D)
  have b := v.map_le_sub ((show (16:WithTop ℤ) ≤ 64 by decide).trans (near 0)) testβ
  exact ⟨by simpa only [sub_sub_cancel] using d,by simpa only [sub_sub_sub_cancel_left] using b⟩

end Sun28.Ordinary
#print axioms Sun28.Ordinary.two_anchor_congruence
#print axioms Sun28.Ordinary.lucas_congruence
#print axioms Sun28.Ordinary.ordinary_precisions
