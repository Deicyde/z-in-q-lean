module

public import Std

@[expose] public section

namespace HeckeShell

/-- Local Euler coefficients after removing the nebentypus phase. -/
def shell (p a k : Int) : Nat → Int
  | 0 => 1
  | 1 => a - k
  | s + 2 => a * shell p a k (s + 1) - p * shell p a k s

/-- Full rational two-torsion writes a_p = p + 1 + 4h. -/
theorem difference_mod_four (p h k : Int) (s : Nat) :
    4 ∣ shell p (p+1+4*h) k (s+1) - shell p (p+1+4*h) k s - p^s*(p-k) := by
  induction s with
  | zero =>
    refine ⟨h, ?_⟩
    simp only [shell, Int.pow_zero, Int.one_mul]
    omega
  | succ s ih =>
    obtain ⟨w, hw⟩ := ih
    let a := p+1+4*h
    change shell p a k (s+1) - shell p a k s - p^s*(p-k) = 4*w at hw
    refine ⟨p*w+h*shell p a k (s+1), ?_⟩
    change a*shell p a k (s+1) - p*shell p a k s - shell p a k (s+1) -
      p^(s+1)*(p-k) = _
    rw [Int.pow_succ]
    dsimp [a] at hw ⊢
    grind

private theorem odd_power (t : Int) (s : Nat) : ∃ w : Int, (2*t+1)^s=2*w+1 := by
  induction s with
  | zero => exact ⟨0, by simp⟩
  | succ s ih =>
    obtain ⟨w, h⟩ := ih
    refine ⟨2*w*t+w+t, ?_⟩
    rw [Int.pow_succ, h]
    grind

/-- For an unramified squarefree part k=±1. The conclusion holds for any odd k. -/
theorem divided_shell (t h z : Int) (s : Nat) :
    let p := 2*t+1
    let a := p+1+4*h
    let k := 2*z+1
    let d := shell p a k (s+1)-shell p a k s
    2 ∣ d ∧ d/2 % 2 = (a-k-1)/2 % 2 := by
  dsimp only
  obtain ⟨w, hw⟩ := difference_mod_four (2*t+1) h (2*z+1) s
  obtain ⟨v, hv⟩ := odd_power t s
  rw [hv] at hw
  have aux : (2*v+1)*(2*t+1-(2*z+1))=4*(v*(t-z))+2*(t-z) := by grind
  rw [aux] at hw
  omega

/-- At a prime dividing the squarefree input, odd square-shell exponents vanish mod two. -/
theorem shared_prime (t h : Int) (s : Nat) :
    let p := 2*t+1
    let a := p+1+4*h
    shell p a 0 s % 2 = 1 - (s : Int) % 2 := by
  dsimp only
  induction s with
  | zero => rfl
  | succ s ih =>
    obtain ⟨w, hw⟩ := difference_mod_four (2*t+1) h 0 s
    obtain ⟨v, hv⟩ := odd_power t s
    rw [hv] at hw
    have aux : (2*v+1)*(2*t+1-0) = 2*(2*v*t+v+t)+1 := by grind
    rw [aux] at hw
    omega

/-- Coefficient k of f(q^a)g(q), listing exactly the possible exponents of f. -/
def dilatedProduct (a : Nat) (f g : Nat → Int) (k : Nat) : Int :=
  ((List.range (k/a+1)).map (fun i => f i * g (k-a*i))).sum

/-- The ordinary U_a passes across a dilated factor in a Fourier product. -/
theorem ordinary_U (a : Nat) (ha : 0 < a) (f g : Nat → Int) (n : Nat) :
    dilatedProduct a f g (a*n) =
      dilatedProduct 1 f (fun k => g (a*k)) n := by
  simp [dilatedProduct, Nat.mul_div_cancel_left _ ha, Nat.mul_sub]

#print axioms difference_mod_four
#print axioms divided_shell
#print axioms shared_prime
#print axioms ordinary_U

end HeckeShell
