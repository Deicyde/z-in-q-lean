import PartialResidual
import Mathlib.NumberTheory.Primorial

namespace Sun28.HeightRefinement.Sharp
open Finset Sun28.FiveMarkUnits Sun28.HeightBudget
noncomputable section
set_option exponentiation.threshold 160
set_option maxRecDepth 8192

/-- The primes in (2^j,2^(j+1)] all divide one central binomial coefficient. -/
theorem block_card (P : Finset ℕ) (pr : ∀ p∈P,p.Prime) {j:ℕ} (pos:0<j)
    (lo:∀ p∈P,2^j<p) (hi:∀ p∈P,p≤2^(j+1)) : P.card≤2^(j+1)/j := by
  let n:ℕ:=2^j
  let C:ℕ:=(n+n).choose n
  have value:2^(j+1)=n+n:=by dsimp [n];rw [pow_succ];omega
  have divides:primeProduct P ∣ C:=by
    apply Finset.prod_primes_dvd
    · intro q h;exact (pr q h).prime
    · intro q h;exact (pr q h).dvd_choose_add (lo q h) (lo q h) (value ▸ hi q h)
  have cap:primeProduct P≤C:=Nat.le_of_dvd (Nat.choose_pos (Nat.le_add_right n n)) divides
  have floor:n^P.card≤primeProduct P:=by
    unfold primeProduct
    rw [←Finset.prod_const (s:=P) (b:=n)]
    exact Finset.prod_le_prod (fun p h=>(lo p h).le)
  have power:2^(j*P.card)≤2^(2^(j+1)):=by
    rw [pow_mul,value];exact (floor.trans cap).trans (Nat.choose_le_two_pow _ _)
  have step: j*P.card≤2^(j+1):=(pow_le_pow_iff_right₀ (by decide:(1:ℕ)<2)).mp power
  exact (Nat.le_div_iff_mul_le pos).mpr (by simpa [Nat.mul_comm] using step)

private def blockLoss (j : ℕ) := (80-4*j)*(2^(j+1)/j)
private def charge (k : ℕ) := 76+∑ i∈range (k-1),blockLoss (i+1)

/-- Small primes pay through the finite dyadic loss, while every prime after
2^20 pays the whole cost through its fourth power. -/
private theorem through {k : ℕ} (pos:1≤k) (cap:k≤20) (P:Finset ℕ)
    (pr:∀ p∈P,p.Prime) (hi:∀ p∈P,p≤2^k) :
    2^(80*P.card)≤2^(charge k)*(primeProduct P)^4 := by
  induction k generalizing P with
  | zero => omega
  | succ j ih =>
    by_cases z:j=0
    · subst j
      have sub:P⊆{2}:=by intro p hp;have l:=(pr p hp).two_le;have u:=hi p hp;rw [pow_one] at u;simpa using le_antisymm u l
      by_cases emp : P=∅
      · subst P;norm_num [primeProduct,charge]
      · have eq:P={2}:= (Finset.subset_singleton_iff.mp sub).resolve_left emp
        rw [eq];norm_num [charge,primeProduct]
    · let L:=P.filter fun p=>p≤2^j
      let R:=P.filter fun p=>¬p≤2^j
      have decomp:P=L∪R:=by ext p;simp only [L,R,mem_union,mem_filter];tauto
      have dis:Disjoint L R:=Finset.disjoint_left.mpr (fun p a b=>(mem_filter.mp b).2 (mem_filter.mp a).2)
      have lp (p) (h:p∈L):p.Prime:=pr _ (mem_filter.mp h).1
      have rp (p) (h:p∈R):p.Prime:=pr _ (mem_filter.mp h).1
      have low (p) (h:p∈R):2^j<p:=Nat.lt_of_not_ge (mem_filter.mp h).2
      have left:=ih (by omega) (by omega) L lp (fun _ h=>(mem_filter.mp h).2)
      have card:=block_card R rp (by omega:0<j) low (fun p h=>hi p (mem_filter.mp h).1)
      have tail : (2^(4*j))^R.card≤(primeProduct R)^4:=by
        have l0 : (2^j)^R.card≤primeProduct R :=by
          unfold primeProduct;rw [←prod_const (s:=R) (b:=2^j)];exact Finset.prod_le_prod (fun p h=>(low p h).le)
        simpa only [←pow_mul,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.pow_le_pow_left l0 4
      have ec : (80-4*j)*R.card≤blockLoss j:=Nat.mul_le_mul_left _ card
      have a : 80*R.card=(80-4*j)*R.card+(4*j)*R.card := by
        rw [←Nat.add_mul];congr 1;omega
      have right:2^(80*R.card)≤2^(blockLoss j)*(primeProduct R)^4:=by
        rw [a,pow_add];exact Nat.mul_le_mul (Nat.pow_le_pow_right (n:=2) (by decide) ec) (by rw [pow_mul (2:ℕ) (4*j)];exact tail)
      have sz:P.card=L.card+R.card:=by conv_lhs=>rw [decomp,Finset.card_union_of_disjoint dis]
      have pp:primeProduct P=primeProduct L*primeProduct R:=by unfold primeProduct;rw [decomp,prod_union dis]
      have ch:charge (j+1)=charge j+blockLoss j:=by
        obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero z
        simp [charge,sum_range_succ,Nat.add_assoc]
      rw [sz,Nat.mul_add,pow_add,ch,pp,pow_add,mul_pow]
      exact (Nat.mul_le_mul left right).trans_eq (mul_mul_mul_comm _ _ _ _)

theorem absorb_quartic (P:Finset ℕ) (pr:∀ p∈P,p.Prime) :
    2^(80*P.card)≤2^1310640*(primeProduct P)^4 := by
  let L:=P.filter fun p=>p≤2^20
  let R:=P.filter fun p=>¬p≤2^20
  have dec:P=L∪R:=by ext p;simp only [L,R,mem_union,mem_filter];tauto
  have dis:Disjoint L R:=Finset.disjoint_left.mpr (fun p a b=>(mem_filter.mp b).2 (mem_filter.mp a).2)
  have bound:=through (k:=20) (by decide) (by decide) L (fun p h=>pr p (mem_filter.mp h).1) (fun _ h=>(mem_filter.mp h).2)
  have charged:charge 20=1005408:=by decide
  generalize he:1310640=budget
  have small:(2:ℕ)^(charge 20)≤2^budget:=Nat.pow_le_pow_right (n:=2) (by decide) (by omega)
  have tail:2^(80*R.card)≤(primeProduct R)^4:=by
    have step:∀p∈R,2^80≤p^4:=by
      intro p hp
      have lo:2^20≤p:=(Nat.lt_of_not_ge (mem_filter.mp hp).2).le
      exact (show (2:ℕ)^80=(2^20)^4 by rw [←pow_mul]).le.trans (Nat.pow_le_pow_left lo _)
    rw [primeProduct,←Finset.prod_pow,pow_mul,←Finset.prod_const (s:=R) (b:=2^80)]
    exact Finset.prod_le_prod step
  have sz:P.card=L.card+R.card:=by conv_lhs=>rw [dec,Finset.card_union_of_disjoint dis]
  have pp:primeProduct P=primeProduct L*primeProduct R:=by unfold primeProduct;rw [dec,prod_union dis]
  rw [sz,Nat.mul_add,pow_add,pp,mul_pow]
  exact (Nat.mul_le_mul (bound.trans (Nat.mul_le_mul_right _ small)) tail).trans_eq (Nat.mul_assoc _ _ _)

open private perm₄ permPairs from PrimeBudget

theorem constant_twelve (P : Finset ℕ) (pr : ∀ p∈P,p.Prime) :
    pellConstant (4*(P.card+1))≤2^1310800*(primeProduct P)^12 := by
  let h:=P.card+1
  let D:=primeProduct P
  have hd : h.factorial≤D:=factorial_le_radical P pr
  have pos : 0<h:=Nat.succ_pos _
  have h4 : h^4≤2^(4*h):=by
    rw [Nat.mul_comm 4 h,pow_mul]
    exact Nat.pow_le_pow_left h.lt_two_pow_self.le _
  have main : h^h≤2^(2*h)*D:=(power_factorial h).trans (Nat.mul_le_mul_left _ hd)
  have expansion : pellConstant (4*h)=2^(60*h+80)*(h^h)^8*h^4:=by
    unfold pellConstant
    let x:=8*h+4
    let z:=8*h+6
    have ex : 2*(4*h)+4=x:=by dsimp [x];omega
    have ez : 2*(4*h)+6=z:=by dsimp [z];omega
    rw [ex,ez,mul_pow]
    have four_pow (u:ℕ) : (4:ℕ)^u=2^(2*u):=by rw [pow_mul];rfl
    have num : (4:ℕ)^x*2^(7*(4*h)+60)*4^z=2^(60*h+80):=by
      rw [four_pow x,four_pow z,←pow_add,←pow_add]
      apply congrArg (fun u:ℕ=>(2:ℕ)^u)
      dsimp [x,z];omega
    have powers : h^x=(h^h)^8*h^4:=by
      rw [←pow_mul,←pow_add]
      apply congrArg (fun u:ℕ=>h^u)
      dsimp [x];omega
    calc
      4^x*h^x*2^(7*(4*h)+60)*4^z = (4^x*2^(7*(4*h)+60)*4^z)*h^x:=by ac_rfl
      _ = _:=by rw [num,powers];ac_rfl
  change pellConstant (4*h)≤2^1310800*D^12
  calc
    _ = _:=expansion
    _ ≤ 2^(60*h+80)*(2^(2*h)*D)^8*2^(4*h):=Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left main _)) h4
    _ = 2^160*2^(80*P.card)*D^8:=by
      rw [mul_pow,←pow_mul]
      let a:=60*h+80
      let b:=2*h*8
      have powers : (2:ℕ)^a*2^b*2^(4*h)=2^160*2^(80*P.card):=by
        rw [←pow_add,←pow_add,←pow_add]
        apply congrArg (fun u:ℕ=>(2:ℕ)^u)
        dsimp [a,b,h];omega
      calc
        _ = (2^a*2^b*2^(4*h))*D^8:=perm₄ _ _ _ _
        _ = _:=by rw [powers]
    _ ≤ 2^160*(2^1310640*D^4)*D^8:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (absorb_quartic P pr))
    _ = _:=by
      calc
        _ = (2^160*2^1310640)*(D^4*D^8):=permPairs _ _ _ _
        _ = _:=by rw [←pow_add,←pow_add]


end
end Sun28.HeightRefinement.Sharp
#print axioms Sun28.HeightRefinement.Sharp.block_card
#print axioms Sun28.HeightRefinement.Sharp.absorb_quartic
#print axioms Sun28.HeightRefinement.Sharp.constant_twelve
