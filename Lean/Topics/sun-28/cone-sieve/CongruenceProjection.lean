import ConeApplication
import ConeScale
import PatternSelection

namespace Sun28.ConeSieve
open Finset Sun28.QuadricSieve Sun28.SinglePrime Sun28.MediumSieve Sun28.ContactFactors
open Sun28.WeightedSelection Sun28.SieveTail Sun28.ContactSieve Filter Topology
open scoped Classical
noncomputable section

/-- Data for an ordinary congruence estimate on one collision quadric.
P consists of the auxiliary sieve primes, with the collision prime removed.
Only intersections of total squarefree modulus at most 2^(2t) are required. -/
def LocalEstimate {A : Fin 3→ℚ} (p : ℕ) [Fact p.Prime] (i j : ↥(shifts A))
    (t W : ℕ) (C D : ℝ) : Prop :=
  ∃ (F : Majorant p i j (lengthAt t) W) (P : Finset ℕ) (g : ℕ→ℝ) (X E : ℝ),
    (∀ q∈P,q.Prime ∧ q≠p ∧ q≤level t ∧ 0≤g q ∧ g q<1 ∧ 1+2*odds g q≤q) ∧
    0≤E ∧
    (2*∑ q∈P,g q*Real.log q≤Real.log (level t)) ∧
    (∀ u⊆P,(∏ q∈u,q)≤(level t)^2 →
      |intersections F.support F.weight (badFactors i P) u-X*(∏ q∈u,g q)|≤E) ∧
    0≤X ∧ 2*X/ (∏ q∈P,(1+odds g q)) ≤
      C*(((lengthAt t):ℝ)*W)/((p:ℝ)^2*(growthBound A t:ℝ)^(shifts A).card) ∧
    (level t:ℝ)^4*E ≤ D*(((lengthAt t):ℝ)*W)/(2:ℝ)^t

theorem diagonal_estimate {A : Fin 3→ℚ} (p : ℕ) [Fact p.Prime] (i : ↥(shifts A))
    (t W : ℕ) {C D : ℝ} (cn : 0≤C) (dn : 0≤D) : LocalEstimate p i i t W C D := by
  have empty : lattice p i i (lengthAt t) W=∅ := by simp [lattice,gap]
  let F : Majorant p i i (lengthAt t) W := ⟨∅,fun _=>0,by simp,by simp [empty],by simp [empty]⟩
  refine ⟨F,∅,fun _=>0,0,0,by simp,le_rfl,?_,?_,le_rfl,?_,?_⟩
  · simp;exact Real.log_nonneg (by exact_mod_cast (show 1≤level t from level_pos t))
  · intro u _ _;simp [F,intersections,mass]
  · simp;positivity
  · simp;positivity

def CongruenceInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ), AdmissibleRoots X c q n →
    let A:=Sun28.RealPoleBounds.fixedScale n
    ∃ (K J : ℕ) (C : ℝ), 0≤C ∧
    ∀ j : ℕ,J≤j → ∃ D : ℝ,0≤D ∧ ∀ᶠ t : ℕ in atTop, ∀ p : ℕ,
      K<p → p≤logCutoff A t → ∀ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        ∀ i k : ↥(shifts A),i≠k → LocalEstimate p i k t (rowWidth j (lengthAt t)) C D

theorem row_of_congruences (input : CongruenceInputs) : FinitePattern.PrimeUpperInputs := by
  classical
  intro X c q n roots d κ T _ _ _ _ H Y
  let A:=Sun28.RealPoleBounds.fixedScale n
  have one : A 0=1 := by simp [A,Sun28.RealPoleBounds.fixedScale,Sun28.Ordinary.scaleRoot]
  obtain ⟨K,J,C,non,rows⟩:=input X c q n roots
  let m:ℝ:=(shifts A).card
  let base := max (max K 2) (max (T.sup id) (κ.primeFactors.sup id))
  refine ⟨base,m^2*C,by dsimp [m];positivity,?_⟩
  intro L bl
  refine ⟨max J (8*(maxCoefficient A+1)),?_⟩
  intro j hj
  obtain ⟨D,dn,est⟩:=rows j ((le_max_left ..).trans hj)
  refine ⟨m^2*D,by dsimp [m];positivity,?_⟩
  filter_upwards [est,eventually_ge_atTop (1:ℕ)] with t row ht
  dsimp only
  intro p hp
  obtain ⟨lo,hi,prime⟩:=mem_places.mp hp
  let _ : Fact p.Prime:=⟨prime⟩
  have outside : p∉T := fun mem=>by have h:=le_sup (f:=id) mem; dsimp [base] at bl; dsimp at h;omega
  have aux : p∉κ.primeFactors := fun mem=>by have h:=le_sup (f:=id) mem; dsimp [base] at bl;dsimp at h;omega
  let W:=rowWidth j (lengthAt t)
  let N:=lengthAt t
  have all:=row p (by dsimp [base] at bl;omega) hi prime
  have eachPair (i k : ↥(shifts A)) : LocalEstimate p i k t W C D := by
    by_cases e : i=k
    · subst k;exact diagonal_estimate p i t W non dn
    · exact all i k e
  choose F P g V E data using eachPair
  have narrow : 8*(maxCoefficient A+1)≤j+1 := by omega
  have up:=one_count_le (H:=H) (Y:=Y) (d:=d) one (by dsimp [base] at bl;omega : p≠2) T outside aux
    P (fun i k r hr=>(data i k).1 r hr |>.1)
    (fun a ha i k r hr s=>((data i k).1 r hr).2.2.1.trans_lt (values_above_level narrow ht ha s)) F
  let B:ℝ:=C*((N:ℝ)*W)/((p:ℝ)^2*(growthBound A t:ℝ)^(shifts A).card)
  let B':ℝ:=D*((N:ℝ)*W)/(2:ℝ)^t
  have each (i k : ↥(shifts A)) : mass (F i k).support (F i k).weight (badFactors i (P i k))
      (fun U=>indicator (U=∅))≤B+B' := by
    obtain ⟨local',en,mean,err,xn,main,small⟩:=data i k
    have pr:=fun r hr=>(local' r hr).1
    have bd:=fun r hr=>(local' r hr).2.2.2
    have both (r : ℕ) (hr : r∈P i k) : 0≤g i k r ∧ g i k r<1 :=
      ⟨(bd r hr).1,(bd r hr).2.1⟩
    have gt : 1<level t := by unfold level;exact Nat.one_lt_pow (by omega) (by decide)
    have den:=half_euler_product (P i k) (g i k) (level t) gt pr both mean
    let Q:=∏ r∈P i k,(1+odds (g i k) r)
    have qp : 0<Q := prod_pos (fun r hr=>by
      have nn : 0≤odds (g i k) r := div_nonneg (both r hr).1 (sub_nonneg.mpr (both r hr).2.le)
      linarith)
    let G:=denominator (g i k) (index (P i k) (level t))
    have ratio : V i k/G ≤ 2*V i k/Q := by
      have eq : 0<G := by change Q≤2*G at den; linarith
      apply (div_le_div_iff₀ eq qp).mpr
      have h:=mul_le_mul_of_nonneg_left den xn
      dsimp [G,Q];linarith only [h]
    exact (upper_bound (F i k).support (F i k).weight (badFactors i (P i k)) (P i k) (g i k)
      (V i k) (E i k) (level t) (level_pos t) (F i k).nonneg pr both
      (fun r hr=>(bd r hr).2.2) en err).trans (add_le_add (ratio.trans main) small)
  apply up.trans
  calc _ ≤ ∑ _ : ↥(shifts A),∑ _ : ↥(shifts A),(B+B') := sum_le_sum (fun i _=>sum_le_sum (fun k _=>each i k))
       _ = _ := by simp [B,B',N,W,m];ring

end
end Sun28.ConeSieve
#print axioms Sun28.ConeSieve.diagonal_estimate
#print axioms Sun28.ConeSieve.row_of_congruences
