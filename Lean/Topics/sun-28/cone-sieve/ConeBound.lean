import ConeWeights

namespace Sun28.ConeSieve
open Finset
noncomputable section
open scoped Classical

def index (P : Finset ℕ) (z : ℕ) := P.powerset.filter (fun r=> ∏ p ∈ r, p ≤ z)

theorem index_card (P : Finset ℕ) (z : ℕ) (pr : ∀ p∈P,p.Prime) : (index P z).card≤z := by
  classical
  let f := fun r : Finset ℕ => ∏ p ∈ r,p
  have prime {r : Finset ℕ} (hr : r∈index P z) (p : ℕ) (hp : p∈r) : p.Prime :=
    pr p (mem_powerset.mp (mem_filter.mp hr).1 hp)
  have inj : Set.InjOn f (↑(index P z)) := by
    intro r hr s hs eq
    have b:=congrArg Nat.primeFactors eq
    simpa [f,Nat.primeFactors_prod (prime hr),Nat.primeFactors_prod (prime hs)] using b
  have sub : (index P z).image f ⊆ Icc 1 z := by
    intro d hd
    obtain ⟨r,hr,rfl⟩:=mem_image.mp hd
    exact mem_Icc.mpr ⟨show 0<f r from prod_pos (fun p hp=>(prime hr p hp).pos),(mem_filter.mp hr).2⟩
  calc _ = ((index P z).image f).card := (card_image_of_injOn inj).symm
       _ ≤ (Icc 1 z).card := card_le_card sub
       _ = z := by simp

theorem coefficient_budget (P : Finset ℕ) (z : ℕ) (g : ℕ → ℝ)
    (non : ∀ p∈P,0≤odds g p)
    (small : ∀ p∈P,1+2*odds g p≤p) {r : Finset ℕ} (hr : r∈index P z) :
    (∑ b∈r.powerset, |coefficient g r b|)≤z := by
  have sub:=mem_powerset.mp (mem_filter.mp hr).1
  rw [coefficient_sum g r (fun p hp=>non p (sub hp))]
  calc _ ≤ ∏ p∈r,(p:ℝ) := prod_le_prod₀ (fun p hp=>by linarith [non p (sub hp)]) (fun p hp=>small p (sub hp))
       _ = ((∏ p∈r,p : ℕ):ℝ) := by simp
       _ ≤ _ := by exact_mod_cast (mem_filter.mp hr).2

/-- Full-cone upper sieve. Only intersections of squarefree modulus at most z² enter the error. -/
theorem upper_bound {α : Type*} (S : Finset α) (w : α → ℝ) (flags : α → Finset ℕ)
    (P : Finset ℕ) (g : ℕ → ℝ) (X E : ℝ) (z : ℕ) (positive : 0<z)
    (wn : ∀ x∈S,0≤w x) (pr : ∀ p∈P,p.Prime) (bounds : ∀ p∈P,0≤g p ∧ g p<1)
    (small : ∀ p∈P,1+2*odds g p≤p) (en : 0≤E)
    (remainder : ∀ u⊆P, (∏ p∈u,p)≤z^2 →
      |intersections S w flags u - X * ∏ p∈u,g p| ≤ E) :
    mass S w flags (fun U=>indicator (U=∅)) ≤ X/denominator g (index P z) + (z:ℝ)^4*E := by
  classical
  let I:=index P z
  let G:=denominator g I
  let Z:ℝ:=z
  have sub {r} (hr : r∈I) : r⊆P := mem_powerset.mp (mem_filter.mp hr).1
  have cap {r} (hr : r∈I) : (∏ p∈r,p)≤z := (mem_filter.mp hr).2
  have pos (p : ℕ) (hp : p∈P) : 0≤odds g p := div_nonneg (bounds p hp).1 (sub_nonneg.mpr (bounds p hp).2.le)
  have gpos : 1≤G := by
    have h : (∅:Finset ℕ)∈I := by simpa [I,index] using (show 1≤z by omega)
    have nn (r : Finset ℕ) (hr : r∈I) : 0≤∏ p∈r,odds g p := prod_nonneg (fun p hp=>pos p (sub hr hp))
    simpa [G,denominator] using single_le_sum nn h
  have zpos : 0≤Z := by positivity
  have entry (r : Finset ℕ) (hr : r∈I) (s : Finset ℕ) (hs : s∈I) :
      mass S w flags (fun U=>basis g r U*basis g s U) ≤
      X*(if r=s then ∏ p∈r,odds g p else 0)+Z^2*E := by
    have gm:=gram_error S w flags P g X E r s (sub hr) (sub hs) (fun p h=>(bounds p h).2)
    have inc {b c : Finset ℕ} (hb : b⊆r) (hc : c⊆s) :
        (∏ p∈b∪c,p)≤z^2 := by
      have mono {a t : Finset ℕ} (h : a⊆t) (inc : t⊆P) :
          (∏ p∈a,p)≤∏ p∈t,p :=
        prod_le_prod_of_subset_of_one_le₀ h (fun _ _=>Nat.zero_le _) (fun p hp _=>(pr p (inc hp)).one_lt.le)
      have u:=prod_union_inter (s₁:=b) (s₂:=c) (f:=fun p : ℕ=>p)
      have one : 0<∏ p∈b∩c,p := prod_pos (fun p h=>(pr p (sub hr (hb (mem_inter.mp h).1))).pos)
      calc _ ≤ (∏ p∈b,p)*(∏ p∈c,p) := u ▸ Nat.le_mul_of_pos_right _ one
           _ ≤ z*z := Nat.mul_le_mul ((mono hb (sub hr)).trans (cap hr)) ((mono hc (sub hs)).trans (cap hs))
           _ = _ := (sq z).symm
    have h:=gm (fun b hb c hc=>remainder (b∪c) (union_subset (hb.trans (sub hr)) (hc.trans (sub hs))) (inc hb hc))
    have b:=mul_le_mul_of_nonneg_right (mul_le_mul (coefficient_budget P z g pos small hr)
      (coefficient_budget P z g pos small hs) (sum_nonneg fun _ _=>abs_nonneg _) zpos) en
    have h':= (le_abs_self _).trans (h.trans b)
    dsimp [Z] at *; linarith only [h']
  have moment : mass S w flags (fun U=>(testSum g I U)^2) ≤ X*G+Z^4*E := by
    have eq : mass S w flags (fun U=>(testSum g I U)^2) =
        ∑ r∈I,∑ s∈I,mass S w flags (fun U=>basis g r U*basis g s U) := by
      unfold mass testSum
      simp only [pow_two,mul_sum,sum_mul]
      rw [sum_comm];apply sum_congr rfl;intro r _;rw [sum_comm]
      apply sum_congr rfl;intro s _
      apply sum_congr rfl;intro x _;ring
    rw [eq]
    apply (sum_le_sum (fun r hr=>sum_le_sum (fun s hs=>entry r hr s hs))).trans
    have card : (I.card:ℝ)≤Z := by dsimp [I,Z];exact_mod_cast index_card P z pr
    have main (r : Finset ℕ) (hr : r∈I) :
        (∑ s∈I, X * (if r=s then ∏ p∈r,odds g p else 0)) = X*(∏ p∈r,odds g p) := by
      rw [←mul_sum];simp [hr]
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_assoc]
    simp_rw [sum_congr rfl main,←mul_sum]
    change X*G+_ ≤ X*G+_
    apply add_le_add_right
    have c:=mul_self_le_mul_self (Nat.cast_nonneg _) card
    have hh:=mul_le_mul_of_nonneg_right c (show 0≤Z^2*E by positivity)
    nlinarith only [hh]
  have surv : mass S w flags (fun U=>indicator (U=∅))*G^2 ≤ mass S w flags (fun U=>(testSum g I U)^2) := by
    dsimp only [mass];rw [sum_mul];apply sum_le_sum;intro x hx
    by_cases live : flags x=∅
    · simp [live,indicator,test_empty,G]
    · simp [indicator,live];exact mul_nonneg (wn x hx) (sq_nonneg _)
  have gg : 0<G^2 := by positivity
  apply ((le_div_iff₀ gg).mpr surv).trans
  have ub:=div_le_div_of_nonneg_right moment gg.le
  apply ub.trans
  have err:0≤Z^4*E := by positivity
  have one : 1≤G^2 := by nlinarith
  have reduce : Z^4*E/G^2≤Z^4*E := div_le_self err one
  rw [add_div,show X*G/G^2=X/G by field_simp [show G≠0 by linarith]]
  exact add_le_add_right reduce _

end
end Sun28.ConeSieve
#print axioms Sun28.ConeSieve.index_card
#print axioms Sun28.ConeSieve.coefficient_budget
#print axioms Sun28.ConeSieve.upper_bound
