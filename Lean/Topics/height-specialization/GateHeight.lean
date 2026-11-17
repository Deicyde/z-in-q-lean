import SelectedComparison

namespace HeightSpecialization
open IndependentIndices IndependentIndices.Assembly
set_option exponentiation.threshold 8192

private def form (a q : Int) := 476*a^2+476*a*q+28*q^2

private theorem form_bound (a : Int) (q u : Nat) (ha : a.natAbs≤u) (hq : q≤u) :
    (form a (q:Int)).natAbs ≤ 980*u^2 := by
  unfold form
  apply Nat.le_trans (Int.natAbs_add_le ..)
  have first := Int.natAbs_add_le (476*a^2) (476*a*(q:Int))
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at *
  have a2:=Nat.pow_le_pow_left ha 2
  have q2:=Nat.pow_le_pow_left hq 2
  have aq:=Nat.mul_le_mul ha hq
  have mid : (476*a*(q:Int)).natAbs ≤ 476*u^2 := by
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    change 476*a.natAbs*q≤476*u^2
    rw [Nat.mul_assoc, Nat.pow_two];exact Nat.mul_le_mul_left _ aq
  have aa : (476*a^2).natAbs ≤ 476*u^2 := by
    simpa only [Int.natAbs_mul,Int.natAbs_pow] using Nat.mul_le_mul_left 476 a2
  have qq : (28*(q:Int)^2).natAbs ≤ 28*u^2 := by
    simpa only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] using Nat.mul_le_mul_left 28 q2
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at aa mid qq
  omega

private theorem height_fraction (a : Int) (q : Nat) (nz : q≠0) :
    H (mkRat a q)≤max a.natAbs q := by
  obtain ⟨g, gn, en, ed⟩ := Rat.normalize_num_den' a q nz
  rw [Rat.normalize_eq_mkRat] at en ed
  have eq:=congrArg Int.natAbs en
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at eq
  have lower (n : Nat) : n≤n*g := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n (show 1≤g by omega)
  apply Nat.max_le.mpr
  constructor
  · calc
      _ ≤ (mkRat a q).num.natAbs*g := lower _
      _ = a.natAbs := eq.symm
      _ ≤ _ := Nat.le_max_left ..
  · calc
      _ ≤ (mkRat a q).den*g := lower _
      _ = q := ed.symm
      _ ≤ _ := Nat.le_max_right ..

/-- Sharp homogeneous height bound for the fixed quartic input label. -/
theorem gate_height (T : Rat) : H (SquareGate.label T) ≤ 962801*(H T)^4 := by
  let a:=T.num
  let q:=T.den
  let F:=2401*(q:Int)^4+(form a q)^2
  have qn : q≠0 := T.den_nz
  have qR : (q:Rat)≠0 := fun h=>qn (Rat.natCast_eq_zero_iff.mp h)
  have val0:=Rat.num_divInt_den T
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at val0
  have val : T*(q:Rat)=(a:Rat) := by
    change T*(T.den:Rat)=(T.num:Rat)
    exact (congrArg (fun k:Rat=>k*(T.den:Rat)) val0.symm).trans (Rat.div_mul_cancel qR)
  have rep : SquareGate.label T=mkRat F (q^4) := by
    rw [Rat.mkRat_eq_div,Rat.natCast_pow]
    have num : SquareGate.label T*(q:Rat)^4=(F:Rat) := by
      dsimp [F,form,SquareGate.label,SquareGate.value,SquareGate.shift]
      simp only [Rat.intCast_add,Rat.intCast_mul,Rat.intCast_pow,Rat.intCast_natCast]
      grobner
    have q4 : (q:Rat)^4≠0 := by grind [Rat.mul_eq_zero]
    exact (Rat.mul_div_cancel (a:=SquareGate.label T) q4).symm.trans
      (congrArg (fun k:Rat=>k/(q:Rat)^4) num)
  have hn : q^4≠0 := Nat.ne_of_gt (Nat.pow_pos (Nat.pos_of_ne_zero qn))
  rw [rep]
  apply Nat.le_trans (height_fraction F _ hn)
  have hq : q≤H T := Nat.le_max_right ..
  have ha : a.natAbs≤H T := Nat.le_max_left ..
  have b := Nat.pow_le_pow_left (form_bound a q _ ha hq) 2
  rw [Nat.mul_pow,←Nat.pow_mul] at b
  change (form a q).natAbs^2 ≤ 960400*(H T)^4 at b
  have q4:=Nat.pow_le_pow_left hq 4
  have t:=Int.natAbs_add_le (2401*(q:Int)^4) ((form a q)^2)
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at t
  change F.natAbs≤2401*q^4+(form a q).natAbs^2 at t
  apply Nat.max_le.mpr
  constructor
  · apply Nat.le_trans t
    exact Nat.le_trans (Nat.add_le_add (Nat.mul_le_mul_left 2401 q4) b) (by omega)
  · omega

theorem gate_height_sharp : H (SquareGate.label 1)=962801 ∧ H 1=1 := by decide +kernel

private theorem small_of_budget (T : Rat) (k : Nat) (height : H T≤2^k)
    (budget : (20+k*4)*17 ≤ anchorModulus-5) : SmallInput T := by
  have fac : 962801≤2^20 := by decide
  have z:=Nat.mul_le_mul fac (Nat.pow_le_pow_left height 4)
  rw [←Nat.pow_mul,←Nat.pow_add] at z
  have cap:=Nat.pow_le_pow_left (Nat.le_trans (gate_height T) z) 17
  rw [←Nat.pow_mul] at cap
  exact Nat.le_trans cap (Nat.pow_le_pow_right (by decide) budget)

/-- A uniform range in which no scalar height estimate or scalar group chart is needed. -/
theorem small_input_of_height (T : Rat) (height : H T≤2^(10^701)) : SmallInput T :=
  small_of_budget T _ height (by decide +kernel)

#print axioms gate_height
#print axioms gate_height_sharp
#print axioms small_input_of_height
end HeightSpecialization
