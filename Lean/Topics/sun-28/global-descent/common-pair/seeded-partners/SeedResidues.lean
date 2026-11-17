import MarkedPartner

namespace Sun28.SeededPartners

/-- Odd squares fill the unit class 1 modulo 8 at precision 128. -/
private theorem choose_residue (v : ZMod 128) (hv : v.val%8=1) :
    ∃ r : Fin 128, (r.val:ZMod 128)^2=v+96 := by
  revert v
  decide +kernel

theorem choose_dyadic (b : ℕ) (bm : b%8=1) :
    ∃ r : ℕ, (r:ZMod 128)^2=(b:ZMod 128)+96 := by
  obtain ⟨r,R⟩:= choose_residue (b:ZMod 128) (by rw [ZMod.val_natCast];omega)
  exact ⟨r.val,R⟩

private theorem odd_square_mod_four (a y : ZMod 4) (h : a*y^2=3) : a=3 := by
  revert a y
  decide +kernel

/-- Writing the first difference as 32(4v+3) exhibits exactly eight
factors of two in the product. Its odd part is 3 modulo four. -/
theorem dyadic_class {b k q h : ℕ} (bm : b%8=1) (high : b<k^2)
    (branch : (k:ZMod 128)^2=(b:ZMod 128)+96) (sf : Squarefree q)
    (dec : (k^2-b)*(9*k^2-b)=q*h^2) : q%4=3 := by
  let D := k^2-b
  have castD : (D:ZMod 128)=96 := by
    dsimp [D]; rw [Nat.cast_sub high.le,Nat.cast_pow,branch];ring
  have modD := congrArg ZMod.val castD
  rw [ZMod.val_natCast] at modD
  change D%128=96 at modD
  let v := D/128
  have V : D=128*v+96 := by dsimp [v];omega
  let u := 4*v+3
  have K : k^2=b+32*u := by dsimp [D,u] at *;omega
  have F : (k^2-b)*(9*k^2-b)=256*(u*(b+36*u)) := by
    rw [K,Nat.add_sub_cancel_left]
    have e : b≤9*(b+32*u) := by omega
    zify [e]
    ring
  have E := F.symm.trans dec
  have qn : q≠0 := sf.ne_zero
  have hn : h≠0 := by rintro rfl;simp [u] at E
  have units : ¬2∣u*(b+36*u) := by
    rw [Nat.prime_two.dvd_mul];dsimp [u];omega
  have nn : u*(b+36*u) ≠ 0 := fun eq=>units (eq ▸ dvd_zero _)
  have V2 := congrArg (padicValNat 2) E
  rw [padicValNat.mul (by decide : 256≠0) nn,
      padicValNat.eq_zero_of_not_dvd units,padicValNat.mul qn (pow_ne_zero _ hn),padicValNat.pow] at V2
  have vq : padicValNat 2 q<2 := by
    by_contra! hi
    have d := (padicValNat_dvd_iff_le qn).mpr hi
    exact (by decide : ¬IsUnit (2:ℕ)) (sf 2 d)
  have vh : 4 ≤ padicValNat 2 h := by
    rw [show padicValNat 2 256=8 by rw [show 256=(2:ℕ)^8 by decide,padicValNat.pow,padicValNat.self];decide] at V2
    omega
  have hd : 2^4∣h := (padicValNat_dvd_iff_le hn).mpr vh
  obtain ⟨y,rfl⟩:=hd
  have core : u*(b+36*u)=q*y^2 := by nlinarith only [E]
  have um : (u:ZMod 4)=3 := by dsimp [u];push_cast;rw [show (4:ZMod 4)=0 by decide];ring
  have b4 : (b:ZMod 4)=1 := (ZMod.natCast_eq_natCast_iff' b 1 4).mpr (by omega)
  have z:=congrArg (fun n:ℕ=>(n:ZMod 4)) core
  push_cast at z
  rw [um,b4] at z
  norm_num at z
  have qmod := odd_square_mod_four q y (z.symm.trans (by decide))
  exact (ZMod.natCast_eq_natCast_iff' q 3 4).mp qmod

end Sun28.SeededPartners
#print axioms Sun28.SeededPartners.choose_dyadic
#print axioms Sun28.SeededPartners.dyadic_class
