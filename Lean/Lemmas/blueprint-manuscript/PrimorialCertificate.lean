import PredecessorHeight
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic
/-! A finite kernel certificate for the product of primes at most 76,176.
Each genuine leaf covers 2,048 consecutive integers. A line with mantissa m
and exponent e bounds the interval product by m · 2^e, rounding the
upper bound upward to 32 binary significant digits. The checker evaluates
the gcd tests only on leaves. Internal nodes compare products of their
certified upper bounds as natural numbers. Each comparison is reduced by
Lean's ordinary kernel. -/
namespace ManuscriptV15.Arithmetic
open scoped BigOperators

/-- An integer in range can be discarded whenever trial division finds a
nontrivial proper divisor. The prime-preservation lemma suffices for an upper bound. -/
private def sieveEntry (n : ℕ) : ℕ :=
  if n = 0 ∨ 76176 < n then 1
  else if Nat.gcd n (Nat.factorial (min 276 (n-1))) = 1 then n else 1

private theorem sieveEntry_pos (n : ℕ) : 1 ≤ sieveEntry n := by
  unfold sieveEntry
  split_ifs <;> omega

private theorem sieveEntry_prime {n : ℕ} (hn : n.Prime) (hmax : n≤76176) : sieveEntry n=n := by
  have hcut : min 276 (n-1) < n :=
    lt_of_le_of_lt (min_le_right _ _) (by have := hn.two_le; omega)
  have hc : Nat.gcd n (Nat.factorial (min 276 (n-1))) = 1 := hn.coprime_factorial_of_lt hcut
  simp [sieveEntry,hn.ne_zero,not_lt.mpr hmax,hc]

/-- Balanced products on dyadic intervals keep the kernel recursion depth
logarithmic in the cutoff, even though the final integer has over 100,000 bits. -/
private def intervalProduct (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, s => f s
  | t+1, s => intervalProduct f t s * intervalProduct f t (s+2^t)

private theorem intervalProduct_eq (f : ℕ → ℕ) (k s : ℕ) :
    intervalProduct f k s = ∏ i ∈ Finset.range (2^k), f (s+i) := by
  induction k generalizing s with
  | zero => simp [intervalProduct]
  | succ k ih =>
    rw [intervalProduct,ih,ih,pow_succ,Nat.mul_two,Finset.prod_range_add]
    simp [Nat.add_comm,Nat.add_left_comm]

private theorem badProduct_le_sieve : badProduct ≤ intervalProduct sieveEntry 17 0 := by
  rw [intervalProduct_eq]
  simp only [zero_add]
  unfold badProduct
  calc (∏ p ∈ (Finset.range 76177).filter Nat.Prime, p) =
      ∏ p ∈ (Finset.range 76177).filter Nat.Prime, sieveEntry p := by
        apply Finset.prod_congr rfl
        intro p hp
        obtain ⟨hr,hp⟩ := Finset.mem_filter.mp hp
        exact (sieveEntry_prime hp (by have := Finset.mem_range.mp hr; omega)).symm
       _ ≤ ∏ p ∈ Finset.range (2^17), sieveEntry p := by
         apply Finset.prod_le_prod_of_subset_of_one_le'
         · intro p hp
           apply Finset.mem_range.mpr
           have h := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
           omega
         · intro p _ _
           exact sieveEntry_pos p

private theorem above_cutoff (k s : ℕ) (hs : 76176 < s) :
    intervalProduct sieveEntry k s = 1 := by
  rw [intervalProduct_eq]
  apply Finset.prod_eq_one
  intro i _
  simp [sieveEntry,show 76176 < s+i by omega]

private theorem join_bounds {k s l r U : ℕ}
    (hl : intervalProduct sieveEntry k s ≤ l)
    (hr : intervalProduct sieveEntry k (s+2^k) ≤ r) (mass : l*r ≤ U) :
    intervalProduct sieveEntry (k+1) s ≤ U :=
  (Nat.mul_le_mul hl hr).trans mass

set_option maxRecDepth 32768
set_option maxHeartbeats 2500000

private theorem b_11_0 : intervalProduct sieveEntry 11 0 ≤ 2998021166 * 2^2833 :=
  by decide +kernel

private theorem b_11_2048 : intervalProduct sieveEntry 11 2048 ≤ 3840395072 * 2^2914 :=
  by decide +kernel

private theorem b_12_0 : intervalProduct sieveEntry 12 0 ≤ 2680715573 * 2^5779 :=
  join_bounds b_11_0 b_11_2048 (by decide +kernel)

private theorem b_11_4096 : intervalProduct sieveEntry 11 4096 ≤ 2384039145 * 2^2887 :=
  by decide +kernel

private theorem b_11_6144 : intervalProduct sieveEntry 11 6144 ≤ 3305808220 * 2^2874 :=
  by decide +kernel

private theorem b_12_4096 : intervalProduct sieveEntry 12 4096 ≤ 3669958656 * 2^5792 :=
  join_bounds b_11_4096 b_11_6144 (by decide +kernel)

private theorem b_13_0 : intervalProduct sieveEntry 13 0 ≤ 2290614723 * 2^11603 :=
  join_bounds b_12_0 b_12_4096 (by decide +kernel)

private theorem b_11_8192 : intervalProduct sieveEntry 11 8192 ≤ 2860184359 * 2^2944 :=
  by decide +kernel

private theorem b_11_10240 : intervalProduct sieveEntry 11 10240 ≤ 2704510545 * 2^2862 :=
  by decide +kernel

private theorem b_12_8192 : intervalProduct sieveEntry 12 8192 ≤ 3602075745 * 2^5837 :=
  join_bounds b_11_8192 b_11_10240 (by decide +kernel)

private theorem b_11_12288 : intervalProduct sieveEntry 11 12288 ≤ 2728560962 * 2^2872 :=
  by decide +kernel

private theorem b_11_14336 : intervalProduct sieveEntry 11 14336 ≤ 4148951167 * 2^3013 :=
  by decide +kernel

private theorem b_12_12288 : intervalProduct sieveEntry 12 12288 ≤ 2635797996 * 2^5917 :=
  join_bounds b_11_12288 b_11_14336 (by decide +kernel)

private theorem b_13_8192 : intervalProduct sieveEntry 13 8192 ≤ 2210574232 * 2^11786 :=
  join_bounds b_12_8192 b_12_12288 (by decide +kernel)

private theorem b_14_0 : intervalProduct sieveEntry 14 0 ≤ 2357910333 * 2^23420 :=
  join_bounds b_13_0 b_13_8192 (by decide +kernel)

private theorem b_11_16384 : intervalProduct sieveEntry 11 16384 ≤ 3271603520 * 2^2927 :=
  by decide +kernel

private theorem b_11_18432 : intervalProduct sieveEntry 11 18432 ≤ 3066100493 * 2^2847 :=
  by decide +kernel

private theorem b_12_16384 : intervalProduct sieveEntry 12 16384 ≤ 2335539360 * 2^5806 :=
  join_bounds b_11_16384 b_11_18432 (by decide +kernel)

private theorem b_11_20480 : intervalProduct sieveEntry 11 20480 ≤ 2793587546 * 2^2919 :=
  by decide +kernel

private theorem b_11_22528 : intervalProduct sieveEntry 11 22528 ≤ 3278561587 * 2^2989 :=
  by decide +kernel

private theorem b_12_20480 : intervalProduct sieveEntry 12 20480 ≤ 4264967898 * 2^5939 :=
  join_bounds b_11_20480 b_11_22528 (by decide +kernel)

private theorem b_13_16384 : intervalProduct sieveEntry 13 16384 ≤ 2319226134 * 2^11777 :=
  join_bounds b_12_16384 b_12_20480 (by decide +kernel)

private theorem b_11_24576 : intervalProduct sieveEntry 11 24576 ≤ 2703596019 * 2^2795 :=
  by decide +kernel

private theorem b_11_26624 : intervalProduct sieveEntry 11 26624 ≤ 3112320865 * 2^3008 :=
  by decide +kernel

private theorem b_12_24576 : intervalProduct sieveEntry 12 24576 ≤ 3918287485 * 2^5834 :=
  join_bounds b_11_24576 b_11_26624 (by decide +kernel)

private theorem b_11_28672 : intervalProduct sieveEntry 11 28672 ≤ 4150332789 * 2^2791 :=
  by decide +kernel

private theorem b_11_30720 : intervalProduct sieveEntry 11 30720 ≤ 4065881234 * 2^2929 :=
  by decide +kernel

private theorem b_12_28672 : intervalProduct sieveEntry 12 28672 ≤ 3928961280 * 2^5752 :=
  join_bounds b_11_28672 b_11_30720 (by decide +kernel)

private theorem b_13_24576 : intervalProduct sieveEntry 13 24576 ≤ 3584381150 * 2^11618 :=
  join_bounds b_12_24576 b_12_28672 (by decide +kernel)

private theorem b_14_16384 : intervalProduct sieveEntry 14 16384 ≤ 3871037829 * 2^23426 :=
  join_bounds b_13_16384 b_13_24576 (by decide +kernel)

private theorem b_15_0 : intervalProduct sieveEntry 15 0 ≤ 4250351385 * 2^46877 :=
  join_bounds b_14_0 b_14_16384 (by decide +kernel)

private theorem b_11_32768 : intervalProduct sieveEntry 11 32768 ≤ 3893253603 * 2^3037 :=
  by decide +kernel

private theorem b_11_34816 : intervalProduct sieveEntry 11 34816 ≤ 4194611161 * 2^2873 :=
  by decide +kernel

private theorem b_12_32768 : intervalProduct sieveEntry 12 32768 ≤ 3802283904 * 2^5942 :=
  join_bounds b_11_32768 b_11_34816 (by decide +kernel)

private theorem b_11_36864 : intervalProduct sieveEntry 11 36864 ≤ 3367139426 * 2^2858 :=
  by decide +kernel

private theorem b_11_38912 : intervalProduct sieveEntry 11 38912 ≤ 2232362905 * 2^2873 :=
  by decide +kernel

private theorem b_12_36864 : intervalProduct sieveEntry 12 36864 ≤ 3500225559 * 2^5762 :=
  join_bounds b_11_36864 b_11_38912 (by decide +kernel)

private theorem b_13_32768 : intervalProduct sieveEntry 13 32768 ≤ 3098708416 * 2^11736 :=
  join_bounds b_12_32768 b_12_36864 (by decide +kernel)

private theorem b_11_40960 : intervalProduct sieveEntry 11 40960 ≤ 2241268049 * 2^3148 :=
  by decide +kernel

private theorem b_11_43008 : intervalProduct sieveEntry 11 43008 ≤ 2398066803 * 2^2792 :=
  by decide +kernel

private theorem b_12_40960 : intervalProduct sieveEntry 12 40960 ≤ 2502794613 * 2^5971 :=
  join_bounds b_11_40960 b_11_43008 (by decide +kernel)

private theorem b_11_45056 : intervalProduct sieveEntry 11 45056 ≤ 2950095903 * 2^2757 :=
  by decide +kernel

private theorem b_11_47104 : intervalProduct sieveEntry 11 47104 ≤ 4204403863 * 2^2970 :=
  by decide +kernel

private theorem b_12_45056 : intervalProduct sieveEntry 12 45056 ≤ 2887890351 * 2^5759 :=
  join_bounds b_11_45056 b_11_47104 (by decide +kernel)

private theorem b_13_40960 : intervalProduct sieveEntry 13 40960 ≤ 3365704983 * 2^11761 :=
  join_bounds b_12_40960 b_12_45056 (by decide +kernel)

private theorem b_14_32768 : intervalProduct sieveEntry 14 32768 ≤ 2428269563 * 2^23529 :=
  join_bounds b_13_32768 b_13_40960 (by decide +kernel)

private theorem b_11_49152 : intervalProduct sieveEntry 11 49152 ≤ 2774878252 * 2^2904 :=
  by decide +kernel

private theorem b_11_51200 : intervalProduct sieveEntry 11 51200 ≤ 3453272822 * 2^2993 :=
  by decide +kernel

private theorem b_12_49152 : intervalProduct sieveEntry 12 49152 ≤ 2231079073 * 2^5929 :=
  join_bounds b_11_49152 b_11_51200 (by decide +kernel)

private theorem b_11_53248 : intervalProduct sieveEntry 11 53248 ≤ 4061051194 * 2^2862 :=
  by decide +kernel

private theorem b_11_55296 : intervalProduct sieveEntry 11 55296 ≤ 3756171606 * 2^3093 :=
  by decide +kernel

private theorem b_12_53248 : intervalProduct sieveEntry 12 53248 ≤ 3551599846 * 2^5987 :=
  join_bounds b_11_53248 b_11_55296 (by decide +kernel)

private theorem b_13_49152 : intervalProduct sieveEntry 13 49152 ≤ 3689853518 * 2^11947 :=
  join_bounds b_12_49152 b_12_53248 (by decide +kernel)

private theorem b_11_57344 : intervalProduct sieveEntry 11 57344 ≤ 2925662026 * 2^2961 :=
  by decide +kernel

private theorem b_11_59392 : intervalProduct sieveEntry 11 59392 ≤ 2440939351 * 2^2764 :=
  by decide +kernel

private theorem b_12_57344 : intervalProduct sieveEntry 12 57344 ≤ 3325456552 * 2^5756 :=
  join_bounds b_11_57344 b_11_59392 (by decide +kernel)

private theorem b_11_61440 : intervalProduct sieveEntry 11 61440 ≤ 2457559591 * 2^2900 :=
  by decide +kernel

private theorem b_11_63488 : intervalProduct sieveEntry 11 63488 ≤ 3780691359 * 2^2828 :=
  by decide +kernel

private theorem b_12_61440 : intervalProduct sieveEntry 12 61440 ≤ 2163293378 * 2^5760 :=
  join_bounds b_11_61440 b_11_63488 (by decide +kernel)

private theorem b_13_57344 : intervalProduct sieveEntry 13 57344 ≤ 3349938495 * 2^11547 :=
  join_bounds b_12_57344 b_12_61440 (by decide +kernel)

private theorem b_14_49152 : intervalProduct sieveEntry 14 49152 ≤ 2877968909 * 2^23526 :=
  join_bounds b_13_49152 b_13_57344 (by decide +kernel)

private theorem b_15_32768 : intervalProduct sieveEntry 15 32768 ≤ 3254266598 * 2^47086 :=
  join_bounds b_14_32768 b_14_49152 (by decide +kernel)

private theorem b_16_0 : intervalProduct sieveEntry 16 0 ≤ 3220461436 * 2^93995 :=
  join_bounds b_15_0 b_15_32768 (by decide +kernel)

private theorem b_11_65536 : intervalProduct sieveEntry 11 65536 ≤ 2637157098 * 2^3045 :=
  by decide +kernel

private theorem b_11_67584 : intervalProduct sieveEntry 11 67584 ≤ 2629119330 * 2^2732 :=
  by decide +kernel

private theorem b_12_65536 : intervalProduct sieveEntry 12 65536 ≤ 3228616297 * 2^5808 :=
  join_bounds b_11_65536 b_11_67584 (by decide +kernel)

private theorem b_11_69632 : intervalProduct sieveEntry 11 69632 ≤ 3169381523 * 2^3013 :=
  by decide +kernel

private theorem b_11_71680 : intervalProduct sieveEntry 11 71680 ≤ 3748306377 * 2^2972 :=
  by decide +kernel

private theorem b_12_69632 : intervalProduct sieveEntry 12 69632 ≤ 2765984502 * 2^6017 :=
  join_bounds b_11_69632 b_11_71680 (by decide +kernel)

private theorem b_13_65536 : intervalProduct sieveEntry 13 65536 ≤ 4158496224 * 2^11856 :=
  join_bounds b_12_65536 b_12_69632 (by decide +kernel)

private theorem b_11_73728 : intervalProduct sieveEntry 11 73728 ≤ 2176028899 * 2^2948 :=
  by decide +kernel

private theorem b_11_75776 : intervalProduct sieveEntry 11 75776 ≤ 2563912564 * 2^520 :=
  by decide +kernel

private theorem b_12_73728 : intervalProduct sieveEntry 12 73728 ≤ 2597993163 * 2^3499 :=
  join_bounds b_11_73728 b_11_75776 (by decide +kernel)

private theorem b_12_77824 : intervalProduct sieveEntry 12 77824 ≤ 1 :=
  (above_cutoff 12 77824 (by decide)).le

private theorem b_13_73728 : intervalProduct sieveEntry 13 73728 ≤ 2597993163 * 2^3499 :=
  join_bounds b_12_73728 b_12_77824 (by decide +kernel)

private theorem b_14_65536 : intervalProduct sieveEntry 14 65536 ≤ 2515442846 * 2^15387 :=
  join_bounds b_13_65536 b_13_73728 (by decide +kernel)

private theorem b_14_81920 : intervalProduct sieveEntry 14 81920 ≤ 1 :=
  (above_cutoff 14 81920 (by decide)).le

private theorem b_15_65536 : intervalProduct sieveEntry 15 65536 ≤ 2515442846 * 2^15387 :=
  join_bounds b_14_65536 b_14_81920 (by decide +kernel)

private theorem b_15_98304 : intervalProduct sieveEntry 15 98304 ≤ 1 :=
  (above_cutoff 15 98304 (by decide)).le

private theorem b_16_65536 : intervalProduct sieveEntry 16 65536 ≤ 2515442846 * 2^15387 :=
  join_bounds b_15_65536 b_15_98304 (by decide +kernel)

private theorem b_17_0 : intervalProduct sieveEntry 17 0 ≤ 3772269320 * 2^109413 :=
  join_bounds b_16_0 b_16_65536 (by decide +kernel)

/-- Integer certificate for the common primorial bound in both predecessor height estimates. -/
theorem badProduct_bit_bound : PrimorialBitBound :=
  lt_of_le_of_lt (badProduct_le_sieve.trans b_17_0) (by decide +kernel)

/-- The older exponent-19 and exponent-24 statements, including both printed bounds
on their logarithms, follow from the single cubic five-contact estimate. -/
theorem predecessorHeights (h : FiveContact) : QuarticHeight19 ∧ O8Height :=
  predecessorHeights_of_fiveContact h badProduct_bit_bound

end ManuscriptV15.Arithmetic
#print axioms ManuscriptV15.Arithmetic.badProduct_bit_bound
#print axioms ManuscriptV15.Arithmetic.predecessorHeights
