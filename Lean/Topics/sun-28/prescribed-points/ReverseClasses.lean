import FamilyLocal
namespace Sun28.PrescribedPoints
open PreparedPoles PairedClasses
open private root_at_beta reduce_family from FamilyLocal

private theorem eight : ∀ t s : ZMod 8, t=1 → Even s →
    (s^2-t)*(9*s^2-t)=1 := by
  intro t s ht hs
  obtain ⟨k,hk⟩ := hs
  subst s
  exact (show ∀ t k : ZMod 8, t=1 → ((k+k)^2-t)*(9*(k+k)^2-t)=1 by decide) t k ht

private theorem removeEight : ∀ b h : ZMod 8, b*h^2=1 → b=1 := by decide

private theorem twentySeven : ∀ a s : Fin 27, a.val%3=1 → s.val^2%27=(a.val+9)%27 →
    (((s.val:ZMod 27)^2-a.val)*(9*(s.val:ZMod 27)^2-a.val))=18 := by decide

private theorem removeThree : ∀ b h : Fin 27, b.val%9≠0 →
    (b.val*h.val^2)%27=18 → b.val%3=2 := by decide

theorem reverse_residue {θ s b h : ℕ} (tm : θ%24=1) (even : 2∣s)
    (sm : s^2 ≡ θ+9 [MOD 27]) (bs : Squarefree b)
    (eq : ((s:ℤ)^2-θ)*(9*(s:ℤ)^2-θ)=(b:ℤ)*h^2) : b%24=17 := by
  have e := reduce_family θ s b h 8 eq
  have ev : Even (s:ZMod 8) := by obtain ⟨k,rfl⟩:=even; exact ⟨k,by push_cast;ring⟩
  have t : (θ:ZMod 8)=1 := (ZMod.natCast_eq_natCast_iff' _ 1 8).mpr (by omega)
  have a := removeEight b h (e.symm.trans (eight θ s t ev))
  have bm : b%8=1 := (ZMod.natCast_eq_natCast_iff' _ 1 8).mp a
  have et := reduce_family θ s b h 27 eq
  have k : (s%27)^2%27=(θ%27+9)%27 := by
    have m : s^2%27=(θ+9)%27 := sm
    simpa only [Nat.pow_mod, Nat.mod_mod, Nat.add_mod] using m
  have ez := twentySeven ⟨θ%27,Nat.mod_lt _ (by decide)⟩ ⟨s%27,Nat.mod_lt _ (by decide)⟩
    (by dsimp;omega) k
  dsimp only at ez
  simp only [ZMod.natCast_mod] at ez
  have bb : (b*h^2)%27=18 := (ZMod.natCast_eq_natCast_iff' _ 18 27).mp
    (by push_cast;exact et.symm.trans ez)
  have nb : ¬9∣b := Nat.squarefree_iff_prime_squarefree.mp bs 3 (by decide)
  have bm3 := removeThree ⟨b%27,Nat.mod_lt _ (by decide)⟩ ⟨h%27,Nat.mod_lt _ (by decide)⟩
    (by dsimp;omega) (by dsimp; simpa only [Nat.mul_mod,Nat.pow_mod,Nat.mod_mod] using bb)
  dsimp only at bm3
  omega

theorem reverse_admissible {θ s b h : ℕ} (tp : 0<θ) (ts : Squarefree θ)
    (tm : θ%24=1) (co : θ.Coprime s) (bp : 0<b) (bs : Squarefree b) (bm : b%24=17)
    (eq : ((s:ℤ)^2-θ)*(9*(s:ℤ)^2-θ)=(b:ℤ)*h^2) : AdmissiblePair b θ := by
  have rootT (p : ℕ) (pp : p.Prime) (dt : p∣θ) :
      let : Fact p.Prime:=⟨pp⟩
      (b:ZMod p)≠0 ∧ IsSquare (b:ZMod p) := by
    let : Fact p.Prime:=⟨pp⟩
    have n : ¬p∣s:=fun d=>pp.not_dvd_one (co ▸ Nat.dvd_gcd dt d)
    have n3 : ¬p∣3:=by intro d; have e:=(Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 3)).mp d;subst p;omega
    exact root_at_beta ((ZMod.natCast_eq_zero_iff _ _).mpr dt) ((ZMod.natCast_eq_zero_iff _ _).not.mpr n)
      (by exact_mod_cast (ZMod.natCast_eq_zero_iff 3 p).not.mpr n3) (reduce_family θ s b h p eq)
  have dis : b.Coprime θ:=by
    by_contra no
    obtain ⟨p,pp,db,dt⟩:=Nat.Prime.not_coprime_iff_dvd.mp no
    exact (rootT p pp dt).1 ((ZMod.natCast_eq_zero_iff _ _).mpr db)
  have six {k : ℕ} (m : k%6=1 ∨ k%6=5) : k.Coprime 6:=by
    change Nat.gcd k 6=1
    rw [Nat.gcd_comm,Nat.gcd_rec]
    rcases m with e|e <;> rw [e] <;> decide
  refine ⟨bp,tp,bs,ts,dis,six (Or.inr (by omega)),six (Or.inl (by omega)),bm,tm,?_,?_⟩
  · intro p pp dt
    let : Fact p.Prime:=⟨pp⟩
    have odd : p≠2:=by rintro rfl;omega
    have z:=rootT p pp dt
    exact local_square_of_legendre odd ((legendreSym.eq_one_iff' p z.1).mpr z.2)
  · intro p pp db
    let : Fact p.Prime:=⟨pp⟩
    have odd : p≠2:=by rintro rfl;omega
    have nz : (θ:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr
      (fun dt=>pp.not_dvd_one (dis ▸ Nat.dvd_gcd db dt))
    apply local_square_of_legendre odd ((legendreSym.eq_one_iff' p nz).mpr ?_)
    have e:=reduce_family θ s b h p eq
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr db,zero_mul] at e
    rcases mul_eq_zero.mp e with f|f
    · exact ⟨s,by linear_combination -f⟩
    · exact ⟨3*(s:ZMod p),by linear_combination -f⟩
end Sun28.PrescribedPoints
#print axioms Sun28.PrescribedPoints.reverse_residue
#print axioms Sun28.PrescribedPoints.reverse_admissible
