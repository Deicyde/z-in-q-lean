import PrimeClassRays

namespace Sun28.PrimeClasses
open ZInQ.Density Sun28.FinitePattern

/-- The signed lift of the trace whose half is one modulo four. -/
def orient (t : ℤ) : ℤ := if t%8=2 then t else -t

theorem oriented_trace {p : ℕ} [Fact p.Prime] (h : InClass p) :
    orient (traceAt p)=2*root p ∧ (orient (traceAt p))^2=(traceAt p)^2 := by
  rcases trace_alternatives h with s|s <;>
    have odd := cp_odd h <;> unfold orient root <;> rw [s] <;>
    split <;> split <;> constructor <;> first | omega | ring

/-- Fixed base ray, expressed in the two characteristic polynomial coefficients. -/
def coefficientBase (n t : ℤ) : Prop :=
  n≡1 [ZMOD 8] ∧ n≡3 [ZMOD 7] ∧ orient t≡18 [ZMOD 32] ∧ orient t≡2 [ZMOD 14] ∧
  4*n≡t^2 [ZMOD 1024]

private theorem scaled (n : ℤ) {a b : ℤ} {s : ℤ} (nz : s≠0) :
    s*a ≡ s*b [ZMOD s*n] ↔ a≡b [ZMOD n] :=
  ⟨Int.ModEq.mul_left_cancel' nz,fun h => h.mul_left'⟩

theorem coefficient_base_iff {p : ℕ} (pp : p.Prime) :
    coefficientBase p (traceAt p) ↔ baseRay p := by
  let _ : Fact p.Prime := ⟨pp⟩
  have aux (h8 : p%8=1) (h7 : p%7=3) :
      (orient (traceAt p) ≡ 18 [ZMOD 32] ∧ orient (traceAt p) ≡ 2 [ZMOD 14] ∧
        4*(p:ℤ) ≡ (traceAt p)^2 [ZMOD 1024]) ↔
      (root p ≡ 9 [ZMOD 16] ∧ root p ≡ 1 [ZMOD 7] ∧
        (p:ℤ) ≡ (root p)^2 [ZMOD 256]) := by
    obtain ⟨o,s⟩ := oriented_trace (p:=p) ⟨h8,Or.inl h7⟩
    rw [←s,o,show (2*root p)^2=4*(root p)^2 by ring]
    exact and_congr (scaled (a:=root p) (b:=9) 16 (by decide : (2:ℤ)≠0))
      (and_congr (scaled (a:=root p) (b:=1) 7 (by decide : (2:ℤ)≠0)) (scaled 256 (by decide : (4:ℤ)≠0)))
  constructor
  · rintro ⟨h8,h7,h⟩
    have a : p%8=1 := Int.natCast_modEq_iff.mp h8
    have b : p%7=3 := Int.natCast_modEq_iff.mp h7
    exact ⟨a,b,(aux a b).mp h⟩
  · rintro ⟨h8,h7,h⟩
    exact ⟨Int.natCast_modEq_iff.mpr h8,Int.natCast_modEq_iff.mpr h7,(aux h8 h7).mpr h⟩

/-- Test on the characteristic polynomial X²−tX+n at the one cutoff. -/
def coefficientClass (L : ℕ) (n t : ℤ) : Prop :=
  coefficientBase n t ∧ ∀ q : ℕ, q.Prime → q≠2 → q≠7 → q≤L → ¬(q:ℤ)∣(n+1)^2-t^2

theorem common_both_iff (L p : ℕ) :
    commonPrime L L p ↔ p.Prime ∧ coefficientClass L p (traceAt p) := by
  rw [common_prime_iff]
  by_cases pp : p.Prime
  · let _ : Fact p.Prime := ⟨pp⟩
    have criterion {q : ℕ} (qp : q.Prime) (base : baseRay p) :
        (¬(q:ℤ)∣signedOrder p true ∧ ¬(q:ℤ)∣signedOrder p false) ↔
          ¬(q:ℤ)∣((p:ℤ)+1)^2-(traceAt p)^2 := by
      obtain ⟨h8,h7,_⟩ := base
      obtain ⟨o,s⟩ := oriented_trace (p:=p) ⟨h8,Or.inl h7⟩
      have eq : ((p:ℤ)+1)^2-(traceAt p)^2=signedOrder p true*signedOrder p false := by
        rw [←s,o]; simp [signedOrder]; ring
      rw [eq,(Nat.prime_iff_prime_int.mp qp).dvd_mul]
      exact not_or.symm
    constructor
    · rintro ⟨_,base,h⟩
      refine ⟨pp,(coefficient_base_iff pp).mpr base,?_⟩
      intro q prime two seven bound
      have a := h q prime two seven bound
      exact (criterion prime base).mp ⟨a.1,a.2 bound⟩
    · rintro ⟨_,base,h⟩
      have b := (coefficient_base_iff pp).mp base
      refine ⟨pp,b,?_⟩
      intro q prime two seven bound
      have a := (criterion prime b).mpr (h q prime two seven bound)
      exact ⟨a.1,fun _ => a.2⟩
  · simp [rationalPrime,pp]

end Sun28.PrimeClasses
#print axioms Sun28.PrimeClasses.oriented_trace
#print axioms Sun28.PrimeClasses.coefficient_base_iff
#print axioms Sun28.PrimeClasses.common_both_iff
