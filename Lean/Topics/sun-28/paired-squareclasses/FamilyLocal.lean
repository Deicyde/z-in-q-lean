import TorsionFamily

namespace Sun28.PairedClasses
open PreparedPoles ZInQ.RouteK

/-- All local assumptions of the manuscript, gathered for a fixed input. -/
def AdmissiblePair (β θ : ℕ) : Prop :=
  0<β ∧ 0<θ ∧ Squarefree β ∧ Squarefree θ ∧
  β.Coprime θ ∧ β.Coprime 6 ∧ θ.Coprime 6 ∧ β%24=17 ∧ θ%24=1 ∧
  (∀ p : ℕ, p.Prime → p∣θ → LocalSquareAt p β) ∧
  (∀ p : ℕ, p.Prime → p∣β → LocalSquareAt p θ)

private theorem mod24_value : ∀ k : ZMod 24,
    ((6*k)^2-17)*(9*(6*k)^2-17)=1 := by decide

set_option maxHeartbeats 2000000 in
private theorem mod24_unit : ∀ t h : ZMod 24, t*h^2=1 → t=1 := by decide

private theorem reduce_family (β k θ h p : ℕ)
    (eq : ((k:ℤ)^2-β)*(9*(k:ℤ)^2-β) = (θ:ℤ)*h^2) :
    ((k:ZMod p)^2-β)*(9*(k:ZMod p)^2-β) = (θ:ZMod p)*h^2 := by
  simpa using congrArg (Int.castRingHom (ZMod p)) eq

private theorem root_at_beta {β k θ h p : ℕ} [Fact p.Prime]
    (b : (β:ZMod p)=0) (kp : (k:ZMod p)≠0) (p3 : (3:ZMod p)≠0)
    (eq : ((k:ZMod p)^2-β)*(9*(k:ZMod p)^2-β) = (θ:ZMod p)*h^2) :
    (θ:ZMod p)≠0 ∧ IsSquare (θ:ZMod p) := by
  have nz : (3*(k:ZMod p)^2)^2≠0 := pow_ne_zero _ (mul_ne_zero p3 (pow_ne_zero _ kp))
  rw [b] at eq
  have e : (3*(k:ZMod p)^2)^2=θ*h^2 := by linear_combination eq
  have hn : (h:ZMod p)≠0 := by rintro zero; apply nz; simpa only [zero,pow_two,zero_mul,mul_zero] using e
  have tn : (θ:ZMod p)≠0 := by rintro zero; apply nz; simpa only [zero,pow_two,zero_mul,mul_zero] using e
  refine ⟨tn,3*(k:ZMod p)^2/h,?_⟩
  field_simp
  linear_combination -e

/-- Every squarefree part of the displayed integer family has Sun's two
mutual local-square conditions. Multiples of six preserve θ = 1 modulo 24. -/
theorem family_admissible {β k θ h : ℕ} (hb : 0<β) (hk : β<k^2)
    (sb : Squarefree β) (st : Squarefree θ) (bc : β.Coprime 6)
    (bk : β.Coprime k) (bm : β%24=17) (six : 6∣k)
    (eq : ((k:ℤ)^2-β)*(9*(k:ℤ)^2-β) = (θ:ℤ)*h^2) :
    AdmissiblePair β θ ∧ Realized β θ := by
  have klt : (β:ℤ)<(k:ℤ)^2 := by exact_mod_cast hk
  have pos : (0:ℤ)<(θ:ℤ)*h^2 := by rw [←eq]; exact mul_pos (by omega) (by omega)
  have tn : θ≠0 := by rintro rfl; simp at pos
  have hn : h≠0 := by rintro rfl; simp at pos
  have modθ : θ%24=1 := by
    obtain ⟨j,ek⟩ := six
    have z := reduce_family β k θ h 24 eq
    rw [ek] at z
    have b : (β:ZMod 24)=17 := (ZMod.natCast_eq_natCast_iff' _ 17 24).mpr bm
    have t := mod24_unit θ h (by rw [←mod24_value j]; simpa [b] using z.symm)
    exact (ZMod.natCast_eq_natCast_iff' _ 1 24).mp t
  have c6 : θ.Coprime 6 := by
    have g : Nat.gcd θ 6=Nat.gcd (θ%6) 6 := (Nat.gcd_comm _ _).trans (Nat.gcd_rec 6 θ)
    change Nat.gcd θ 6=1
    rw [g,show θ%6=1 by omega]
    decide
  have rootB (p : ℕ) (pp : p.Prime) (db : p∣β) :
      let : Fact p.Prime := ⟨pp⟩
      (θ:ZMod p)≠0 ∧ IsSquare (θ:ZMod p) := by
    let : Fact p.Prime := ⟨pp⟩
    have bk' : ¬p∣k := fun dk => pp.not_dvd_one (bk ▸ Nat.dvd_gcd db dk)
    have b3 : ¬p∣3 := fun d3 => pp.not_dvd_one (bc ▸ Nat.dvd_gcd db (d3.trans (by decide)))
    exact root_at_beta ((ZMod.natCast_eq_zero_iff _ _).mpr db)
      ((ZMod.natCast_eq_zero_iff _ _).not.mpr bk') (by exact_mod_cast (ZMod.natCast_eq_zero_iff 3 p).not.mpr b3)
      (reduce_family β k θ h p eq)
  have disjoint : β.Coprime θ := by
    by_contra nd
    obtain ⟨p,pp,db,dt⟩ := Nat.Prime.not_coprime_iff_dvd.mp nd
    exact (rootB p pp db).1 ((ZMod.natCast_eq_zero_iff _ _).mpr dt)
  refine ⟨⟨hb,Nat.pos_of_ne_zero tn,sb,st,disjoint,bc,c6,bm,modθ,?_,?_⟩,?_⟩
  · intro p pp dt
    let : Fact p.Prime := ⟨pp⟩
    have no2 : p≠2 := by rintro rfl; omega
    have bn : (β:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr
      (fun db => pp.not_dvd_one (disjoint ▸ Nat.dvd_gcd db dt))
    have e := reduce_family β k θ h p eq
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr dt,zero_mul] at e
    apply local_square_of_legendre no2 ((legendreSym.eq_one_iff' p bn).mpr ?_)
    rcases mul_eq_zero.mp e with f|f
    · exact ⟨k,by linear_combination -f⟩
    · exact ⟨3*(k:ZMod p),by linear_combination -f⟩
  · intro p pp db
    let : Fact p.Prime := ⟨pp⟩
    have no2 : p≠2 := by rintro rfl;omega
    have ⟨nz,root⟩ := rootB p pp db
    exact local_square_of_legendre no2 ((legendreSym.eq_one_iff' p nz).mpr root)
  · apply realized_of_family hb (Nat.pos_of_ne_zero tn) sb (bc.mul_right disjoint)
    exact ⟨k,h,by exact_mod_cast hn,by exact_mod_cast eq⟩

/-- A producer from integer inputs. The factorization only chooses the ordinary
positive squarefree part of a specified integer. -/
theorem family_of_index {β k : ℕ} (hb : 0<β) (hk : β<k^2) (sb : Squarefree β)
    (bc : β.Coprime 6) (bk : β.Coprime k) (bm : β%24=17) (six : 6∣k) :
    ∃ θ h : ℕ, (k^2-β)*(9*k^2-β) = θ*h^2 ∧ AdmissiblePair β θ ∧ Realized β θ := by
  let P := (k^2-β)*(9*k^2-β)
  have nine : β<9*k^2 := by omega
  have ppos : 0<P := Nat.mul_pos (by omega) (by omega)
  obtain ⟨h,_,e⟩ := sqfNat_mul_sq ppos.ne'
  refine ⟨sqfNat P,h,e,family_admissible (h:=h) hb hk sb (sqfNat_squarefree P) bc bk bm six ?_⟩
  have cast := congrArg (fun z : ℕ => (z:ℤ)) e
  simpa only [P,Nat.cast_mul,Nat.cast_sub hk.le,Nat.cast_sub nine.le,Nat.cast_pow,
    Nat.cast_ofNat] using cast

theorem example_17_5833 : AdmissiblePair 17 5833 ∧ Realized 17 5833 := by
  have s17 := (show Nat.Prime 17 by decide).squarefree
  have s5833 : Squarefree 5833 := (Nat.squarefree_mul (show Nat.Coprime 19 307 by decide)).mpr
    ⟨(show Nat.Prime 19 by decide).squarefree,(show Nat.Prime 307 by norm_num).squarefree⟩
  exact family_admissible (k:=6) (h:=1) (by decide) (by decide) s17 s5833
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- A point on each of the two literal curves, using the coprime squarefree
parameter 731 for the previously studied pair (17,409). -/
theorem example_17_409 : Realized 17 409 := by
  have s731 : Squarefree 731 := (Nat.squarefree_mul (show Nat.Coprime 17 43 by decide)).mpr
    ⟨(show Nat.Prime 17 by decide).squarefree,(show Nat.Prime 43 by decide).squarefree⟩
  refine ⟨731,by decide,s731,by decide,?_,?_⟩
  · refine ⟨7691/944,17*(7691/944)*(13195/944)*(18819/944),by norm_num,?_⟩
    norm_num
  · refine ⟨16834486001/8855428,
      17*(16834486001/8855428)*(16956926695/8855428)*(69241267359/8855428),by norm_num,?_⟩
    norm_num

end Sun28.PairedClasses
#print axioms Sun28.PairedClasses.family_admissible

#print axioms Sun28.PairedClasses.family_of_index
#print axioms Sun28.PairedClasses.example_17_5833

#print axioms Sun28.PairedClasses.example_17_409
