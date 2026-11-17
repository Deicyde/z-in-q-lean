import FiveContacts
import InputRestriction

namespace StructuralHeights
open InputRestriction

/-- Extract a positive squarefree kernel from an arbitrary positive natural number. -/
theorem squarefree_decomposition (n : Nat) (positive : 0<n) :
    ∃ d s : Nat, Squarefree d ∧ 0<d ∧ 0<s ∧ n=d*s^2 := by
  classical
  by_cases sf : Squarefree n
  · exact ⟨n,1,sf,positive,by decide,by simp⟩
  have bad : ∃ a : Nat, a^2 ∣ n ∧ a≠1 := by
    apply Classical.byContradiction
    intro none
    exact sf (fun a h=>Classical.byContradiction fun neq=>none ⟨a,h,neq⟩)
  obtain ⟨a,⟨b,eq⟩,different⟩ := bad
  have az : a≠0 := by intro z;simp [z] at eq;omega
  have bz : 0<b := by
    by_cases z : b=0
    · simp [z] at eq;omega
    · omega
  have big : 1<a^2 := by
    have h := Nat.pow_le_pow_left (show 2≤a by omega) 2
    omega
  have smaller : b<n := eq ▸ (Nat.lt_mul_iff_one_lt_left bz).mpr big
  obtain ⟨d,s,sfd,dp,sp,bs⟩ := squarefree_decomposition b bz
  exact ⟨d,a*s,sfd,dp,Nat.mul_pos (by omega) sp,by rw [eq,bs];grobner⟩
termination_by n

private theorem squarefree_odd_iff {p d : Nat} (hp : Prime p) (sf : Squarefree d) :
    OddOrder p (d:Int) ↔ p∣d := by
  constructor
  · intro h
    exact Int.ofNat_dvd.mp (odd_dvd h)
  · rintro ⟨b,eq⟩
    have unit : ¬p∣b := by
      rintro ⟨a,eq'⟩
      have h : p^2 ∣ d := ⟨a,by rw [eq,eq'];grobner⟩
      have := sf p h
      have := hp.1
      omega
    refine ⟨0,(b:Int),?_,fun h=>unit (Int.ofNat_dvd.mp h)⟩
    rw [eq,Int.natCast_mul]; change (p:Int)*(b:Int)=(p:Int)^1*(b:Int); grobner

/-- The squarefree kernel encodes the full odd support, prime by prime. -/
theorem kernel_support (n : Nat) (positive : 0<n) :
    ∃ d s : Nat, Squarefree d ∧ 0<s ∧ n=d*s^2 ∧
      ∀ p, Prime p → (OddOrder p (n:Int) ↔ p∣d) := by
  obtain ⟨d,s,sf,_,sp,eq⟩ := squarefree_decomposition n positive
  refine ⟨d,s,sf,sp,eq,fun p hp=>?_⟩
  rw [eq,Int.natCast_mul,Int.natCast_pow,odd_times_square hp (show (s:Int)≠0 by omega)]
  exact squarefree_odd_iff hp sf

private theorem prime_factor (n : Nat) (large : 1<n) : ∃ p, Prime p ∧ p∣n := by
  classical
  by_cases h : Prime n
  · exact ⟨n,h,Nat.dvd_refl _⟩
  have middle : ∃ a, a∣n ∧ a≠1 ∧ a≠n := by
    apply Classical.byContradiction
    intro none
    exact h ⟨large,fun a ha=>by
      by_cases one : a=1
      · exact Or.inl one
      · exact Or.inr (Classical.byContradiction fun ne=>none ⟨a,ha,one,ne⟩)⟩
  obtain ⟨a,ha,one,ne⟩:=middle
  have zero : a≠0 := by intro z;simp [z] at ha;omega
  have le := Nat.le_of_dvd (by omega : 0<n) ha
  have smaller : a<n := by omega
  obtain ⟨p,hp,d⟩ := prime_factor a (by omega)
  exact ⟨p,hp,Nat.dvd_trans d ha⟩
termination_by n

/-- A squarefree integer divides every integer containing its prime support. -/
theorem squarefree_dvd_of_support (n b : Nat) (pos : 0<n) (sf : Squarefree n)
    (supported : ∀ p, Prime p → p∣n → p∣b) : n∣b := by
  by_cases one : n=1
  · simp [one]
  obtain ⟨p,hp,dp⟩:=prime_factor n (by omega)
  obtain ⟨k,eq⟩:=dp
  have big := hp.1
  have kp : 0<k := by
    by_cases z : k=0
    · simp [z] at eq;omega
    · omega
  have smaller : k<n := eq ▸ (Nat.lt_mul_iff_one_lt_left kp).mpr big
  have sfk : Squarefree k := fun a ha=>sf a (Nat.dvd_trans ha ⟨p,by rw [eq];grobner⟩)
  have primeNotK : ¬p∣k := by
    rintro ⟨a,e⟩
    have h := sf p ⟨a,by rw [eq,e];grobner⟩
    omega
  obtain ⟨b',eb⟩ := supported p hp ⟨k,eq⟩
  have rest (q : Nat) (hq : Prime q) (dq : q∣k) : q∣b' := by
    have inN : q∣n := Nat.dvd_trans dq ⟨p,by rw [eq];grobner⟩
    have inB := supported q hq inN
    rw [eb] at inB
    have inZ : (q:Int)∣(p:Int)*(b':Int) := by simpa only [Int.natCast_mul] using Int.ofNat_dvd.mpr inB
    rcases (prime_dvd_mul hq).mp inZ with left|right
    · rcases hp.2 q (Int.ofNat_dvd.mp left) with z|z
      · have := hq.1;omega
      · exact False.elim (primeNotK (z ▸ dq))
    · exact Int.ofNat_dvd.mp right
  obtain ⟨w,ew⟩ := squarefree_dvd_of_support k b' kp sfk rest
  exact ⟨w,by rw [eb,eq,ew];grobner⟩
termination_by n

#print axioms squarefree_dvd_of_support
#print axioms squarefree_decomposition
#print axioms kernel_support
end StructuralHeights
