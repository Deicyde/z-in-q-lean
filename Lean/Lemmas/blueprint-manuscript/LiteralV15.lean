import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Hyperoperation

namespace ManuscriptV15
open MvPolynomial

/-- Coordinate slots are zero-based in Lean. The decoder accepts the manuscript's one-based slots. -/
structure Row (n : ℕ) where
  coefficient : ℤ
  parameterPower : ℕ
  slots : List (Fin n)

def parseSlot (n : ℕ) (s : String) : Option (Fin n) := do
  let k ← s.toNat?
  if h : 0 < k ∧ k ≤ n then return ⟨k-1,by omega⟩ else none

def parseRow (n : ℕ) (s : String) : Option (Row n) := do
  match s.splitOn " " with
  | c :: e :: vars => return ⟨←c.toInt?, ←e.toNat?, ←vars.mapM (parseSlot n)⟩
  | _ => none

def parseRows (n : ℕ) (s : String) : Option (List (Row n)) :=
  ((s.splitOn "\n").filter (· != "")).mapM (parseRow n)

def fixedText := include_str "data/v15-314.txt"
def familyText := include_str "data/v15-222.txt"

noncomputable def fromRows {n : ℕ} (a : ℤ) (rows : List (Row n)) : MvPolynomial (Fin n) ℤ :=
  rows.foldl (fun p row => p + C (row.coefficient * a ^ row.parameterPower) *
      (row.slots.map (fun i => (X i : MvPolynomial (Fin n) ℤ))).prod) 0

def A (N : ℕ) : ℤ := 149 ^ (2*N+1)
noncomputable def fixedTable := (parseRows 314 fixedText).map (fromRows 1)
noncomputable def familyTable (N : ℕ) := (parseRows 222 familyText).map (fromRows (A N))

def DefinesIntegers {m : ℕ} (P : MvPolynomial (Fin (m+1)) ℤ) : Prop :=
  ∀ q : ℚ, (∃ w : Fin m → ℚ, MvPolynomial.eval₂ (Int.castRingHom ℚ) (Fin.cons q w) P = 0) ↔
    ∃ z : ℤ, (z : ℚ) = q

def Primitive {n : ℕ} (P : MvPolynomial (Fin n) ℤ) : Prop :=
  ∀ g : ℕ, (∀ m, g ∣ (P.coeff m).natAbs) → g = 1

/-- The assertions of thm:v15-decimal, with the ordinary coefficient table fixed. -/
def Fixed314 : Prop := ∃ P : MvPolynomial (Fin 314) ℤ, fixedTable = some P ∧
  P.totalDegree = 4 ∧ Primitive P ∧ P.support.card = 6672 ∧
  (∀ m, (P.coeff m).natAbs < 2^6496) ∧ DefinesIntegers P

/-- V15 thm:v15-main. The arithmetic threshold is independent of the numerical cutoff 53. -/
def Family222 : Prop := ∃ F : ℕ → MvPolynomial (Fin 222) ℤ,
  (∀ N, familyTable N = some (F N)) ∧
  (∃ N₀ : ℕ, ∀ N ≥ N₀, DefinesIntegers (F N)) ∧
  (∀ N, (F N).totalDegree = 4 ∧ Primitive (F N)) ∧
  ∀ N ≥ 53, (F N).support.card = 2277 ∧
    (∀ m, ((F N).coeff m).natAbs ≤ (A N ^ 2 + 1).natAbs) ∧
    ∃ m, ((F N).coeff m).natAbs = (A N ^ 2 + 1).natAbs

/-- Any requested lower cutoff can be imposed after the arithmetic threshold is supplied. -/
theorem defining_member_above (h : Family222) (cutoff : ℕ) :
    ∃ N ≥ cutoff, ∃ P : MvPolynomial (Fin 222) ℤ, familyTable N = some P ∧
      DefinesIntegers P ∧ P.totalDegree = 4 ∧ P.support.card = 2277 := by
  obtain ⟨F,tab,⟨threshold,good⟩,deg,profile⟩ := h
  let N := max threshold (max 53 cutoff)
  have hn : threshold ≤ N := le_max_left ..
  have hr : max 53 cutoff ≤ N := le_max_right ..
  exact ⟨N,(le_max_right ..).trans hr,F N,tab N,good N hn,(deg N).1,
    (profile N ((le_max_left ..).trans hr)).1⟩

/-- The frozen public target, using the exact arity and strict hyperoperation bounds. -/
def Frozen : Prop := ∃ P : MvPolynomial (Fin 292890231905) ℤ,
  P.totalDegree < hyperoperation 4 2 7 ∧
  (∀ m : Fin 292890231905 →₀ ℕ, (P.coeff m).natAbs < hyperoperation 4 2 8) ∧
  DefinesIntegers P

def includeFin {m n : ℕ} (h : m ≤ n) : Fin m ↪ Fin n :=
  ⟨fun i => ⟨i.val,lt_of_lt_of_le i.isLt h⟩, fun _ _ e => Fin.ext (congrArg (fun j : Fin n => j.val) e)⟩

private theorem cons_include {m n : ℕ} (h : m ≤ n) (q : ℚ) (w : Fin n → ℚ) :
    Fin.cons (α:=fun _ => ℚ) q w ∘ includeFin (Nat.succ_le_succ h) =
      Fin.cons (α:=fun _ => ℚ) q (w ∘ includeFin h) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Fin.cons (α:=fun _ => ℚ) q w 0 = Fin.cons (α:=fun _ => ℚ) q (w ∘ includeFin h) 0
    simp
  · change Fin.cons (α:=fun _ => ℚ) q w (includeFin h j).succ =
      Fin.cons (α:=fun _ => ℚ) q (w ∘ includeFin h) j.succ
    simp

/-- Renaming the first coordinates into a larger block preserves both existential directions. -/
theorem padding_projection {m n : ℕ} (h : m ≤ n) (P : MvPolynomial (Fin (m+1)) ℤ) :
    DefinesIntegers (rename (includeFin (Nat.succ_le_succ h)) P) ↔ DefinesIntegers P := by
  have eqv (q : ℚ) :
      (∃ v : Fin n → ℚ, eval₂ (Int.castRingHom ℚ) (Fin.cons q v)
        (rename (includeFin (Nat.succ_le_succ h)) P) = 0) ↔
      ∃ w : Fin m → ℚ, eval₂ (Int.castRingHom ℚ) (Fin.cons q w) P = 0 := by
    constructor
    · rintro ⟨v,hv⟩
      rw [eval₂_rename,cons_include h q v] at hv
      exact ⟨v ∘ includeFin h,hv⟩
    · rintro ⟨w,hw⟩
      let v : Fin n → ℚ := fun i => if t : i.val < m then w ⟨i.val,t⟩ else 0
      have hv : v ∘ includeFin h = w := by funext i; simp [v,includeFin,i.isLt]
      refine ⟨v,?_⟩
      rw [eval₂_rename,cons_include h q v,hv]
      exact hw
  exact ⟨fun H q => (eqv q).symm.trans (H q),fun H q => (eqv q).trans (H q)⟩

private theorem tower_step (k : ℕ) : hyperoperation 4 2 (k+1) = 2 ^ hyperoperation 4 2 k :=
  (hyperoperation_recursion 3 2 k).trans (hyperoperation_three 2 _)

private theorem tower_bounds : 4 < hyperoperation 4 2 7 ∧ 2^6496 < hyperoperation 4 2 8 := by
  have growth (k : ℕ) : hyperoperation 4 2 k < hyperoperation 4 2 (k+1) := by
    rw [tower_step]; exact Nat.lt_two_pow_self
  have small : hyperoperation 4 2 4 = 65536 := by
    rw [tower_step 3,tower_step 2,tower_step 1,tower_step 0]
    rw [hyperoperation_ge_three_eq_one 1 2]
    decide
  have large : hyperoperation 4 2 4 < hyperoperation 4 2 7 :=
    lt_trans (lt_trans (growth 4) (growth 5)) (growth 6)
  rw [small] at large
  have exponentBound : 6496 < hyperoperation 4 2 7 := Nat.lt_trans (by decide : 6496 < 65536) large
  refine ⟨by omega,?_⟩
  rw [tower_step 7]
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) exponentBound

/-- The literal fixed quartic, with its stated coefficient bounds and projection,
    implies the frozen public theorem by leaving all the additional variables unused. -/
theorem fixed314_to_frozen (h : Fixed314) : Frozen := by
  obtain ⟨P,_,deg,_,_,coeff,proj⟩ := h
  let i := includeFin (show 314 ≤ 292890231905 by decide)
  refine ⟨rename i P,?_,?_,?_⟩
  · exact (totalDegree_rename_le i P).trans_lt (deg ▸ tower_bounds.1)
  · intro m
    by_cases zero : (rename i P).coeff m = 0
    · rw [zero]; exact lt_trans (Nat.pow_pos (by decide : 0 < 2)) tower_bounds.2
    · obtain ⟨u, rfl, _⟩ := coeff_rename_ne_zero i P m zero
      rw [coeff_rename_mapDomain i i.injective]
      exact (coeff u).trans tower_bounds.2
  · exact (padding_projection (show 313 ≤ 292890231904 by decide) P).mpr proj

end ManuscriptV15
