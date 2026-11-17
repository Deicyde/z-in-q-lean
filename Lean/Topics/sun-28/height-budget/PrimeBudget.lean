import SquareSupport

namespace Sun28.HeightBudget
open Sun28.FiveMarkUnits
set_option exponentiation.threshold 160
set_option maxHeartbeats 1000000
open Finset
noncomputable section

private theorem perm₄ (a b c d:ℕ) : a*(b*c)*d=(a*b*d)*c:=by ac_rfl
private theorem permPairs (a b c d:ℕ) : a*(b*c)*d=(a*b)*(c*d):=by ac_rfl

/-- The (j+1)-st ordered prime is at least j+2. -/
theorem factorial_le_radical (P : Finset ℕ) (pr : ∀ p∈P,p.Prime) :
    (P.card+1).factorial≤primeProduct P := by
  induction P using Finset.induction_on_max with
  | empty => simp [primeProduct]
  | insert a s larger ih =>
    have pa := pr a (Finset.mem_insert_self ..)
    have ps (p) (h:p∈s) := pr p (Finset.mem_insert_of_mem h)
    have na : a∉s:=fun h=>(larger a h).false
    have sub : s⊆Ico 2 a:=fun x hx=>mem_Ico.mpr ⟨(ps x hx).two_le,larger x hx⟩
    have card:=Finset.card_le_card sub
    rw [Nat.card_Ico] at card
    have a2:=pa.two_le
    have lt : s.card+2≤a:=by omega
    rw [Finset.card_insert_of_notMem na,Nat.factorial_succ]
    unfold primeProduct
    rw [Finset.prod_insert na]
    exact Nat.mul_le_mul lt (ih ps)

/-- The factorial is within 4^h of h^h, without Stirling approximation. -/
theorem power_factorial (h : ℕ) : h^h≤2^(2*h)*h.factorial := by
  calc
    h^h ≤ h.ascFactorial h:=Nat.pow_succ_le_ascFactorial _ _
    _ = _:=Nat.ascFactorial_eq_factorial_mul_choose' h h
    _ ≤ h.factorial*2^(2*h):=Nat.mul_le_mul_left _ ((Nat.choose_le_two_pow _ _).trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
    _ = _:=mul_comm ..

/-- A prime at least 16384 contributes six powers to absorb 80 powers of two. -/
theorem absorb_places (P : Finset ℕ) (pr : ∀ p∈P,p.Prime) :
    2^(80*P.card)≤2^1310640*(primeProduct P)^6 := by
  classical
  generalize he : 1310640 = exponent
  let L : ℕ := 16384
  let u:=P.filter fun p=>p<L
  let v:=P.filter fun p=>¬p<L
  have decomp : P=u∪v:=by ext p; simp only [u,v,Finset.mem_union,Finset.mem_filter];tauto
  have disj : Disjoint u v:=Finset.disjoint_left.mpr (fun _ a b=>(Finset.mem_filter.mp b).2 (Finset.mem_filter.mp a).2)
  have ub : u⊆Ico 1 L:=by
    intro p m
    obtain ⟨inP,lt⟩:=Finset.mem_filter.mp m
    exact mem_Ico.mpr ⟨(pr p inP).pos,lt⟩
  have count : u.card≤16383:=(card_le_card ub).trans (by rw [Nat.card_Ico];decide)
  have cover (p) (m:p∈v) : 2^80≤p^6:=by
    have lo : 16384≤p:=le_of_not_gt (Finset.mem_filter.mp m).2
    exact (by decide : 2^80≤16384^6).trans (Nat.pow_le_pow_left lo _)
  have tail : 2^(80*v.card)≤(primeProduct v)^6:=by
    rw [primeProduct,←Finset.prod_pow, pow_mul, ←Finset.prod_const (s:=v) (b:=2^80)]
    exact Finset.prod_le_prod cover
  have expBound : 80*u.card≤exponent:=by omega
  have small := Nat.pow_le_pow_right (n:=2) (by decide) expBound
  have subv : v⊆P:=Finset.filter_subset _ _
  have mono := Sun28.MinimalConductors.support_mono subv pr
  rw [show P.card=u.card+v.card by conv_lhs=>rw [decomp,Finset.card_union_of_disjoint disj],
    Nat.mul_add,pow_add]
  exact Nat.mul_le_mul (n₁:=2^(80*u.card)) (n₂:=2^exponent) (m₁:=2^(80*v.card)) (m₂:=(primeProduct P)^6) small (tail.trans (Nat.pow_le_pow_left mono _))

/-- Raw s-place, degree-four constant of Bérczes, Evertse and Győry. -/
def pellConstant (s : ℕ) := s^(2*s+4)*2^(7*s+60)*4^(2*s+6)

theorem constant_bound (P : Finset ℕ) (pr : ∀ p∈P,p.Prime) :
    pellConstant (4*(P.card+1))≤2^1310800*(primeProduct P)^14 := by
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
  change pellConstant (4*h)≤2^1310800*D^14
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
    _ ≤ 2^160*(2^1310640*D^6)*D^8:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (absorb_places P pr))
    _ = _:=by
      calc
        _ = (2^160*2^1310640)*(D^6*D^8):=permPairs _ _ _ _
        _ = _:=by rw [←pow_add,←pow_add]

end
end Sun28.HeightBudget
#print axioms Sun28.HeightBudget.factorial_le_radical
#print axioms Sun28.HeightBudget.power_factorial
#print axioms Sun28.HeightBudget.absorb_places
#print axioms Sun28.HeightBudget.constant_bound
