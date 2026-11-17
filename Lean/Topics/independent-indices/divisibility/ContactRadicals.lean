import ContactResidues

namespace IndependentIndices
open Lean.Grind

structure Residue (N : Nat) where
  carrier : Type
  ring : CommRing carrier
  characteristic : letI := ring; IsCharP carrier N

def Residue.finite (N : Nat) [NeZero N] : Residue N :=
  ⟨Fin N,inferInstance,inferInstance⟩

/-- Each comparison keeps its own index. Local ratios and residue rings may vary with the prime. -/
structure Contact (p : Nat) (m : Int) (ns : Labels) (B : Rat) where
  odd : p%2=1
  ten : Residue (p^10)
  forty : Residue (p^40)
  rows : @Ratios ten.carrier forty.carrier ten.ring forty.ring m ns B

theorem Contact.divides {p m ns B} (c : Contact p m ns B) :
    ((p^40:Nat):Int) ∣ lucas ns.n₂ ns.n₃ ns.n₄ ∧ ((p^10:Nat):Int) ∣ ((ns.n₁:Rat)-B).num := by
  letI := c.ten.ring
  letI := c.ten.characteristic
  letI := c.forty.ring
  letI := c.forty.characteristic
  exact local_divisibilities p c.odd c.rows

def radical : List Nat → Nat
  | [] => 1
  | p::ps => Nat.lcm p (radical ps)

def product : List Nat → Nat
  | [] => 1
  | p::ps => p*product ps

private theorem coprime_product (p : Nat) (ps : List Nat) (h : ∀ q∈ps,p.Coprime q) :
    p.Coprime (product ps) := by
  induction ps with
  | nil => simp [product,Nat.Coprime]
  | cons q qs ih => exact (h q (by simp)).mul_right (ih (fun r hr=>h r (List.mem_cons_of_mem _ hr)))

theorem radical_eq_product (ps : List Nat) (pairwise : ps.Pairwise Nat.Coprime) :
    radical ps=product ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have h:=List.pairwise_cons.mp pairwise
    simp only [radical,product,ih h.2,Nat.lcm_eq_mul_div,(coprime_product p ps h.1).gcd_eq_one,Nat.div_one]

/-- Elementary primality as needed only for identifying the lcm with the usual radical product. -/
def IsContactPrime (p : Nat) := 1<p ∧ ∀ d, d∣p → d=1 ∨ d=p

theorem prime_list_radical (ps : List Nat) (unique : ps.Nodup) (prime : ∀p∈ps,IsContactPrime p) :
    radical ps=product ps := by
  apply radical_eq_product
  induction ps with
  | nil => exact List.Pairwise.nil
  | cons p tail ih =>
    have distinct:=List.pairwise_cons.mp unique
    apply List.pairwise_cons.mpr;constructor
    · intro q hq
      have fresh := distinct.1 q hq
      have h1:=(prime p (by simp)).2 _ (Nat.gcd_dvd_left p q)
      have h2:=(prime q (by simp [hq])).2 _ (Nat.gcd_dvd_right p q)
      rcases h1 with a|a
      · exact a
      · rcases h2 with b|b
        · exact b
        · exact False.elim (fresh (a.symm.trans b))
    · exact ih distinct.2 (fun q h=>prime q (List.mem_cons_of_mem _ h))

theorem aggregate (k : Nat) (z : Int) (ps : List Nat)
    (atEach : ∀ p∈ps, ((p^k:Nat):Int)∣z) : ((radical ps ^ k:Nat):Int)∣z := by
  apply Int.ofNat_dvd_left.mpr
  induction ps with
  | nil => simp [radical]
  | cons p ps ih =>
    rw [radical,←Nat.pow_lcm_pow]
    exact Nat.lcm_dvd (Int.ofNat_dvd_left.mp (atEach p (by simp))) (ih (fun q h=>atEach q (List.mem_cons_of_mem _ h)))

theorem radical_append (ps qs : List Nat) : radical (ps++qs)=Nat.lcm (radical ps) (radical qs) := by
  induction ps with
  | nil => simp [radical]
  | cons p ps ih => simp only [List.cons_append,radical,ih,Nat.lcm_assoc]

def Defects (j : Nat) (ns : Labels) (B : Rat) :=
  ((j^40:Nat):Int) ∣ lucas ns.n₂ ns.n₃ ns.n₄ ∧ ((j^10:Nat):Int) ∣ ((ns.n₁:Rat)-B).num

structure Frame (ns : Labels) (B : Rat) where
  m : Int
  primes : List Nat
  observations : ∀ p∈primes, Nonempty (Contact p m ns B)

theorem Frame.defects {ns B} (f : Frame ns B) : Defects (radical f.primes) ns B := by
  constructor
  · apply aggregate;intro p hp;obtain ⟨c⟩:=f.observations p hp;exact c.divides.1
  · apply aggregate;intro p hp;obtain ⟨c⟩:=f.observations p hp;exact c.divides.2

theorem lcm_defects {a b ns B} (ha : Defects a ns B) (hb : Defects b ns B) : Defects (Nat.lcm a b) ns B := by
  have combine {k : Nat} {z : Int} (x : ((a^k:Nat):Int)∣z) (y : ((b^k:Nat):Int)∣z) :
      (((Nat.lcm a b)^k:Nat):Int)∣z := by
    rw [←Nat.pow_lcm_pow];exact Int.ofNat_dvd_left.mpr (Nat.lcm_dvd (Int.ofNat_dvd_left.mp x) (Int.ofNat_dvd_left.mp y))
  exact ⟨combine ha.1 hb.1,combine ha.2 hb.2⟩

def largest (a b c : Nat) := max a (max b c)

private theorem either_max {a b : Nat} {P : Nat→Prop} (ha : P a) (hb : P b) : P (max a b) := by
  rcases Nat.le_total a b with z|z
  · simpa only [Nat.max_eq_right z] using hb
  · simpa only [Nat.max_eq_left z] using ha

/-- The maximum is attained at one actual comparison; overlap requires no arithmetic here. -/
theorem three_max {a b c : Nat} {P : Nat→Prop} (ha : P a) (hb : P b) (hc : P c) : P (largest a b c) :=
  either_max ha (either_max hb hc)

theorem largest_bounds (a b c : Nat) : a≤largest a b c ∧ b≤largest a b c ∧ c≤largest a b c := by
  unfold largest;omega

theorem three_frames {ns B} (f g h : Frame ns B) :
    let a:=radical f.primes
    let b:=radical g.primes
    let c:=radical h.primes
    Defects (Nat.lcm a (Nat.lcm b c)) ns B ∧ Defects (largest a b c) ns B := by
  exact ⟨lcm_defects f.defects (lcm_defects g.defects h.defects),
    three_max (P:=fun j=>Defects j ns B) f.defects g.defects h.defects⟩

/-- Each nonzero defect gives a numerical bound on the largest observed radical at its own order. -/
theorem largest_powers_le {ns B} (f g h : Frame ns B) :
    let M:=largest (radical f.primes) (radical g.primes) (radical h.primes)
    let F:=lucas ns.n₂ ns.n₃ ns.n₄
    let numerator:=((ns.n₁:Rat)-B).num
    (F≠0 → M^40≤F.natAbs) ∧ (numerator≠0 → M^10≤numerator.natAbs) := by
  have d:=(three_frames f g h).2
  exact ⟨fun hn=>Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.ofNat_dvd_left.mp d.1),
         fun hn=>Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.ofNat_dvd_left.mp d.2)⟩

end IndependentIndices
