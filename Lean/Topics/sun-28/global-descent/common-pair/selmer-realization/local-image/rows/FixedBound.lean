import FiniteImage
import PrimeDecomposition
import SignedWordEncoding
import SmallMarkedImage
import OddUnitRows
import OddImages
import ZInQKernel.RouteK.Selmer.Prop0

namespace Sun28.FixedLocalRows
open Sun28.SelmerRealization ZInQ.RouteK
noncomputable section

theorem supported {a b : ℤ} (h : (a,b) ∈ localClasses n) :
    WordEncoding.Supported a ∧ WordEncoding.Supported b := by
  obtain ⟨sa,sb,_,loc⟩ := h
  have primes_of {p : ℕ} (pp : p.Prime) (d : p∣n) : p∈WordEncoding.primes := by
    change p∣11*(109*(439*(283*(1433*(4373*14557))))) at d
    simp only [pp.dvd_mul] at d
    rcases d with d|d|d|d|d|d|d <;>
      have E := (Nat.prime_dvd_prime_iff_eq pp (by norm_num)).mp d <;>
      simp [E,WordEncoding.primes]
  have outside (p:ℕ) (pp:p.Prime) (ex:p∉WordEncoding.primes) : ¬(p:ℤ)∣a ∧ ¬(p:ℤ)∣b := by
    let : Fact p.Prime := ⟨pp⟩
    have nt : p≠2 := fun eq=> ex (by simp [eq,WordEncoding.primes])
    have ns : p≠3 := fun eq=> ex (by simp [eq,WordEncoding.primes])
    exact Sun28.MarkedOdd.good_support nt ns (fun d=>ex (primes_of pp d)) sa sb (loc p)
  constructor
  · apply WordEncoding.supported_of_prime_divisors
    intro p pp d
    by_contra away
    exact (outside p pp away).1 d
  · apply WordEncoding.supported_of_prime_divisors
    intro p pp d
    by_contra away
    exact (outside p pp away).2 d

private theorem fixed_squarefree : Squarefree n := by
  change Squarefree (11*(109*(439*(283*(1433*(4373*14557))))) : ℕ)
  simp only [Nat.squarefree_mul_iff]
  repeat' first | constructor | exact (by norm_num : Nat.Prime _).squarefree

private theorem verified_prime {p:ℕ} (hp : p∈badPrimes) :
    p.Prime ∧ p≠2 ∧ p≠3 ∧ p∣n ∧ (n:ℤ)=(p:ℤ)*(fixedN/p) ∧ ¬(p:ℤ)∣(fixedN/p) := by
  simp [badPrimes] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [n,fixedN]

private theorem false_of_zero {b : Bool} (h : parity b=0) : b=false := by
  cases b <;> simp_all [parity]

private theorem two_eq_zero {x y z : ZMod 2} (h:x=y+z) : x+y+z=0 := by
  subst x
  revert y z
  decide
private theorem one_eq_zero {x y : ZMod 2} (h:x=y) : x+y=0 := by
  subst x
  revert y
  decide

theorem prime_pair {a b : ℤ} (v : Word) (pair : FixedLocalRows.labels v=(a,b))
    {p : ℕ} (hp : p∈badPrimes) (loc : ∀ (p:ℕ) [Fact p.Prime], Cover ℚ_[p] n a b) :
    bitDot (localRow p false) 0 v=false ∧ bitDot (localRow p true) 0 v=false := by
  obtain ⟨pr,p2,p3,pn,N,mun⟩ := verified_prime hp
  let : Fact p.Prime := ⟨pr⟩
  have h := List.mem_cons_of_mem 3 hp
  obtain ⟨x,hx,A,ordA⟩ := decomposition h v 0
  obtain ⟨y,hy,B,ordB⟩ := decomposition h v 10
  have pa : generatorProduct generators 0 v = a := congrArg Prod.fst pair
  have pb : generatorProduct generators 10 v = b := congrArg Prod.snd pair
  rw [pa] at A
  rw [pb] at B
  have au := (unit_character (generators.map (unitFactor p)) 0 v (prime_units p h)).1
  have bu := (unit_character (generators.map (unitFactor p)) 10 v (prime_units p h)).1
  obtain ⟨r,t⟩ := Sun28.MarkedOdd.bad_rows_of_decomposition p2 p3 pn fixed_squarefree hx hy A B N au bu mun (loc p)
  rw [ordA,ordB] at r
  rw [ordB] at t
  exact ⟨false_of_zero ((row_value_a p hp v).trans (two_eq_zero r)),
    false_of_zero ((row_value_b p hp v).trans (one_eq_zero t))⟩

/-- The fixed local coverings lie in the eight explicitly listed signed classes. -/
theorem local_label_list {a b : ℤ} (h : (a,b)∈localClasses n) :
    (a,b)∈([(1,1),(526361,1),(25815704738179,1),(13588380161692636619,1),
      (3,-13588380161692636619),(1579083,-13588380161692636619),
      (77447114214537,-13588380161692636619),(40765140485077909857,-13588380161692636619)] :
      List (ℤ×ℤ)) := by
  obtain ⟨sa,sb⟩ := supported h
  have pa := h.1
  have pb := h.2.1
  have loc := h.2.2.2
  obtain ⟨ap,_,b2,b3,_⟩ := Sun28.SmallImage.local_small h
  let v := WordEncoding.encode a b
  have pair : FixedLocalRows.labels v = (a,b) := WordEncoding.labels_encode pa pb sa sb
  have f0 : v.getLsbD 0=false := by
    exact (WordEncoding.encode_sign_bits a b).1.trans (by simp [not_lt.mpr ap.le])
  have f11 : v.getLsbD 11=false := by
    have e := (WordEncoding.encode_prime_bits pa pb (0:Fin 9)).2
    change v.getLsbD 11=decide ((2:ℤ)∣b) at e
    exact e.trans (by simp [show ¬(2:ℤ)∣b by omega])
  have f12 : v.getLsbD 12=false := by
    have e := (WordEncoding.encode_prime_bits pa pb (1:Fin 9)).2
    change v.getLsbD 12=decide ((3:ℤ)∣b) at e
    exact e.trans (by simp [show ¬(3:ℤ)∣b by omega])
  have order3 : orderBit 3 10 v=0 := by
    have e := congrArg parity f12
    have t : (orderBit 3 10 v) = parity (v.getLsbD 12) := by
      simp [orderBit,generators,total,parity]
    exact t.trans e
  obtain ⟨j,hj,decj,ord⟩ := decomposition (p:=3) (by simp) v 10
  have jz : j=0 := by
    rw [order3] at ord
    interval_cases j <;> norm_num at *
  have pb' : generatorProduct generators 10 v=b := congrArg Prod.snd pair
  rw [pb',jz,pow_zero,one_mul] at decj
  have congr : b ≡ 1 [ZMOD 3] := (show b%3=1%3 by omega)
  have char : legBit 3 b=0 := (legBit_congr congr).trans (by simp [legBit])
  have t := false_of_zero ((row_three v).trans (decj ▸ char))
  have primeChecks : ∀p∈badPrimes, bitDot (localRow p false) 0 v=false ∧ bitDot (localRow p true) 0 v=false :=
    fun _ hp => prime_pair v pair hp loc
  have arithmetic : arithmeticEquations v := by
    refine ⟨?_,f0,f11,f12,t⟩
    apply List.all_eq_true.mpr
    intro w mem
    have pMem : w.1∈badPrimes := by
      change w∈badPrimes.zipIdx at mem
      have q := List.mem_map_of_mem (f:=Prod.fst) mem
      simpa using q
    obtain ⟨A,B⟩ := primeChecks _ pMem
    simp [A,B]
  rw [←pair]
  exact eight_labels arithmetic

theorem fixed_upper : ∃ c : Finset (ℤ×ℤ), c.card≤8 ∧ localClasses n ⊆ (c:Set (ℤ×ℤ)) := by
  let s : List (ℤ×ℤ) := [(1,1),(526361,1),(25815704738179,1),(13588380161692636619,1),
      (3,-13588380161692636619),(1579083,-13588380161692636619),
      (77447114214537,-13588380161692636619),(40765140485077909857,-13588380161692636619)]
  refine ⟨s.toFinset,by decide,?_⟩
  rintro ⟨a,b⟩ h
  exact List.mem_toFinset.mpr (local_label_list h)

/-- For the prepared pair the only remaining input besides Mordell--Weil
finite generation is a point of infinite order on the first curve. -/
theorem fixed_scalar [AddGroup.FG (RationalPoint n)]
    (point : ∃ P:RationalPoint n, ¬IsOfFinAddOrder P) :
    ∃ e z : ℚ, Sun28.Ordinary.poleBranch 15 Sun28.PointFibres.pole e z :=
  Sun28.MarkedDescent.prepared_scalar_of_upper fixed_upper point

end
end Sun28.FixedLocalRows
#print axioms Sun28.FixedLocalRows.supported
#print axioms Sun28.FixedLocalRows.prime_pair

#print axioms Sun28.FixedLocalRows.local_label_list
#print axioms Sun28.FixedLocalRows.fixed_upper
#print axioms Sun28.FixedLocalRows.fixed_scalar
