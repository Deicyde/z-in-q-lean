import SeededRealization
import ZInQKernel.RouteK.Selmer.PadicSquare

namespace Sun28.MarkedDescent
open Sun28.SelmerRealization ZInQ.RouteK.Selmer
noncomputable section
abbrev mark : ℤ := 526361

theorem cover_of_square {K : Type*} [Field K] [CharZero K]
    (h : IsSquare (mark:K)) : Cover K n mark 1 := by
  obtain ⟨r,R⟩:=h
  refine ⟨1,r,1,0,Or.inl one_ne_zero,?_,?_⟩
  · simp only [Int.cast_one,mul_one,one_mul,one_pow,zero_pow (by decide : 2≠0),mul_zero];linear_combination R
  · push_cast;ring

theorem cover_of_square_multiplier {K : Type*} [Field K] [CharZero K]
    (h : IsSquare ((Sun28.SelmerRealization.multiplier:ℕ):K)) : Cover K n mark 1 := by
  obtain ⟨r,R⟩:=h
  have N : (n:K)=(mark:K)*(r*r) := by
    have h := congrArg (fun z:ℕ=>(z:K)) n_shape.1
    push_cast at h
    simpa only [mark,Int.cast_ofNat,R] using h
  refine ⟨r,0,2*r,1,Or.inr (Or.inr (Or.inr one_ne_zero)),?_,?_⟩ <;> rw [N] <;> push_cast <;> ring

theorem fixed_archimedean : Cover ℝ n mark 1 :=
  cover_of_square ((Real.isSquare_iff).mpr (by norm_num [mark]))

theorem fixed_dyadic : Cover ℚ_[2] n mark 1 := by
  apply cover_of_square
  have H := isSquare_intCast_div_two_adic (m:=mark) (n:=1) (by decide) (by decide)
  simpa only [Int.cast_one,div_one] using H

private theorem localRoot3 : ((25815704738179:ℤ):ZMod 3)=(1:ZMod 3)*1 := by decide +kernel

private theorem localRoot11 : ((25815704738179:ℤ):ZMod 11)=(2:ZMod 11)*2 := by decide +kernel

private theorem localRoot109 : ((25815704738179:ℤ):ZMod 109)=(26:ZMod 109)*26 := by decide +kernel

private theorem localRoot439 : ((25815704738179:ℤ):ZMod 439)=(151:ZMod 439)*151 := by decide +kernel

private theorem localRoot283 : ((526361:ℤ):ZMod 283)=(84:ZMod 283)*84 := by decide +kernel

private theorem localRoot1433 : ((526361:ℤ):ZMod 1433)=(162:ZMod 1433)*162 := by decide +kernel

private theorem localRoot4373 : ((526361:ℤ):ZMod 4373)=(1735:ZMod 4373)*1735 := by decide +kernel

private theorem localRoot14557 : ((526361:ℤ):ZMod 14557)=(1655:ZMod 14557)*1655 := by decide +kernel

theorem fixed_bad_primes (p : ℕ) [Fact p.Prime] (bad : p ∣ 6*n) :
    Cover ℚ_[p] n mark 1 := by
  have parts : 6*n=2*(3*(11*(109*(439*(283*(1433*(4373*14557))))))) := by decide
  rw [parts] at bad
  have hp := Fact.out (p:=Nat.Prime p)
  have prime_factor {q : ℕ} (hq : q.Prime) (div : p ∣ q) : p=q :=
    ((Nat.dvd_prime hq).mp div).resolve_left hp.ne_one
  simp only [Nat.Prime.dvd_mul hp] at bad
  rcases bad with H|H|H|H|H|H|H|H|H
  · obtain rfl := prime_factor (by norm_num) H
    exact fixed_dyadic
  · obtain rfl := prime_factor (by norm_num) H
    apply cover_of_square_multiplier
    exact isSquare_intCast_of_residue (p:=3) (c:=25815704738179) (by decide) (by decide) ⟨1,by exact localRoot3⟩
  · obtain rfl := prime_factor (by norm_num) H
    apply cover_of_square_multiplier
    exact isSquare_intCast_of_residue (p:=11) (c:=25815704738179) (by decide) (by decide) ⟨2,by exact localRoot11⟩
  · obtain rfl := prime_factor (by norm_num) H
    apply cover_of_square_multiplier
    exact isSquare_intCast_of_residue (p:=109) (c:=25815704738179) (by decide) (by decide) ⟨26,by exact localRoot109⟩
  · obtain rfl := prime_factor (by norm_num) H
    apply cover_of_square_multiplier
    exact isSquare_intCast_of_residue (p:=439) (c:=25815704738179) (by decide) (by decide) ⟨151,by exact localRoot439⟩
  · obtain rfl := prime_factor (by norm_num) H
    exact cover_of_square (isSquare_intCast_of_residue (p:=283) (c:=mark) (by decide) (by decide) ⟨84,by exact localRoot283⟩)
  · obtain rfl := prime_factor (by norm_num) H
    exact cover_of_square (isSquare_intCast_of_residue (p:=1433) (c:=mark) (by decide) (by decide) ⟨162,by exact localRoot1433⟩)
  · obtain rfl := prime_factor (by norm_num) H
    exact cover_of_square (isSquare_intCast_of_residue (p:=4373) (c:=mark) (by decide) (by decide) ⟨1735,by exact localRoot4373⟩)
  · obtain rfl := prime_factor (by norm_num) H
    exact cover_of_square (isSquare_intCast_of_residue (p:=14557) (c:=mark) (by decide) (by decide) ⟨1655,by exact localRoot14557⟩)

end
end Sun28.MarkedDescent
#print axioms Sun28.MarkedDescent.cover_of_square
#print axioms Sun28.MarkedDescent.cover_of_square_multiplier
#print axioms Sun28.MarkedDescent.fixed_archimedean
#print axioms Sun28.MarkedDescent.fixed_dyadic
#print axioms Sun28.MarkedDescent.fixed_bad_primes
