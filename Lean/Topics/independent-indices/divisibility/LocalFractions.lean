import ContactRadicals

namespace IndependentIndices

/-- Rational elements representable with positive denominator prime to the base modulus
and numerator a multiple of the indicated scale. Scale one is the integral local ring. -/
def fractionLayer (base scale : Nat) (x : Rat) : Prop :=
  ∃ a : Int, ∃ d : Nat, 0<d ∧ d.Coprime base ∧ x*(d:Rat)=(scale:Rat)*(a:Rat)

def fractionError (N : Nat) (x : Rat) : Prop := fractionLayer N N x

private theorem odd_coprime (N : Nat) (h : N%2=1) : Nat.Coprime 2 N := by
  change Nat.gcd 2 N=1
  rw [Nat.gcd_def];simp [h]

def layerModule (N scale : Nat) (odd : N%2=1) : ErrorModule Rat where
  contains := fractionLayer N scale
  add := by
    rintro x y ⟨a,d,hd,dc,hx⟩ ⟨b,e,he,ec,hy⟩
    refine ⟨a*(e:Int)+b*(d:Int),d*e,Nat.mul_pos hd he,dc.mul_left ec,?_⟩
    simp only [Rat.natCast_mul,Rat.intCast_add,Rat.intCast_mul,Rat.intCast_natCast];grobner
  sub := by
    rintro x y ⟨a,d,hd,dc,hx⟩ ⟨b,e,he,ec,hy⟩
    refine ⟨a*(e:Int)-b*(d:Int),d*e,Nat.mul_pos hd he,dc.mul_left ec,?_⟩
    simp only [Rat.natCast_mul,Rat.intCast_sub,Rat.intCast_mul,Rat.intCast_natCast];grobner
  intMul := by
    rintro i x ⟨a,d,hd,dc,hx⟩
    exact ⟨i*a,d,hd,dc,by rw [Rat.intCast_mul];grobner⟩
  half := by
    rintro x ⟨a,d,hd,dc,hx⟩
    refine ⟨a,2*d,Nat.mul_pos (by decide) hd,(odd_coprime N odd).mul_left dc,?_⟩
    rw [Rat.natCast_mul];change x*(2*(d:Rat))=_;grobner

def fractionModule (N : Nat) (odd : N%2=1) : ErrorModule Rat := layerModule N N odd

private theorem clear_canonical (x : Rat) : x*(x.den:Rat)=(x.num:Rat) := by
  have nz : (x.den:Rat)≠0 := fun h=>x.den_nz (Rat.natCast_eq_zero_iff.mp h)
  have eq:=Rat.num_divInt_den x
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at eq
  exact (congrArg (fun q : Rat=>q*(x.den:Rat)) eq.symm).trans (Rat.div_mul_cancel nz)

theorem local_integral_iff (N : Nat) (x : Rat) : fractionLayer N 1 x ↔ x.den.Coprime N := by
  constructor
  · rintro ⟨a,d,_,dc,eq⟩
    have canonical:=clear_canonical x
    have cross : x.num*(d:Int)=a*(x.den:Int) := by
      apply Rat.intCast_inj.mp
      simp only [Rat.intCast_mul,Rat.intCast_natCast]
      change x*(d:Rat)=1*(a:Rat) at eq;grobner
    have hd : (x.den:Int)∣x.num*(d:Int) := by rw [cross];apply Int.dvd_mul_left
    have hn:=Int.ofNat_dvd_left.mp hd
    rw [Int.natAbs_mul,Int.natAbs_natCast] at hn
    have hdvd:=x.reduced.symm.dvd_of_dvd_mul_left hn
    exact Nat.Coprime.coprime_dvd_left hdvd dc
  · intro h
    refine ⟨x.num,x.den,x.den_pos,h,?_⟩
    change x*(x.den:Rat)=1*(x.num:Rat)
    rw [clear_canonical,Rat.one_mul]

theorem rational_bootstrap (p : Nat) (odd : p%2=1) (m : Int) (l l' : Rat)
    (cross : (l-l').den.Coprime p) (left : ((m:Rat)*l).den.Coprime p)
    (right : (((m:Rat)-2)*l').den.Coprime p) : l.den.Coprime p ∧ l'.den.Coprime p := by
  have h:=bootstrap (layerModule p 1 odd) m l l'
    ((local_integral_iff ..).mpr cross) ((local_integral_iff ..).mpr left) ((local_integral_iff ..).mpr right)
  exact ⟨(local_integral_iff ..).mp h.1,(local_integral_iff ..).mp h.2⟩

theorem fraction_num {N : Nat} {x : Rat} (h : fractionError N x) : (N:Int)∣x.num := by
  obtain ⟨a,d,_,dc,eq⟩:=h
  have canonical:=clear_canonical x
  have he : x.num*(d:Int)=(N:Int)*a*(x.den:Int) := by
    apply Rat.intCast_inj.mp
    simp only [Rat.intCast_mul,Rat.intCast_natCast];grobner
  have mult : (N:Int) ∣ x.num*(d:Int) := ⟨a*(x.den:Int),by rw [he,Int.mul_assoc]⟩
  have natural:=Int.ofNat_dvd_left.mp mult
  rw [Int.natAbs_mul,Int.natAbs_natCast] at natural
  exact Int.ofNat_dvd_left.mpr (dc.symm.dvd_of_dvd_mul_right natural)

/-- The reduced numerator test supplies the canonical denominator's coprimality as well. -/
theorem detector_denominator {N : Nat} {n : Int} {B : Rat}
    (h : (N:Int) ∣ ((n:Rat)-B).num) : B.den.Coprime N := by
  rw [reduced_num] at h
  let d:=Nat.gcd B.den N
  have hd : (d:Int)∣(B.den:Int) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left B.den N)
  have hn : (d:Int)∣(N:Int) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right B.den N)
  have mult : (d:Int)∣n*(B.den:Int) := Int.dvd_trans hd (Int.dvd_mul_left _ _)
  have sub := Int.dvd_sub mult (Int.dvd_trans hn h)
  rw [show n*(B.den:Int)-(n*(B.den:Int)-B.num)=B.num from by grobner] at sub
  have one : d∣1 := by
    rw [←B.reduced.gcd_eq_one]
    exact Nat.dvd_gcd (Int.ofNat_dvd_left.mp sub) (Nat.gcd_dvd_left _ _)
  exact Nat.dvd_antisymm one (Nat.one_dvd _)

theorem fraction_iff_canonical {N : Nat} (x : Rat) :
    fractionError N x ↔ (N:Int)∣x.num ∧ x.den.Coprime N := by
  constructor
  · intro h
    have num:=fraction_num h
    have neg : (N:Int)∣((0:Int).cast - x : Rat).num := by
      rw [reduced_num];simp only [Int.zero_mul,Int.zero_sub,Int.dvd_neg];exact num
    exact ⟨num,detector_denominator neg⟩
  · rintro ⟨⟨k,eq⟩,hc⟩
    refine ⟨k,x.den,x.den_pos,hc,?_⟩
    rw [clear_canonical,eq,Rat.intCast_mul,Rat.intCast_natCast]

/-- For rational coefficients the two local log comparisons can be supplied as explicit
fractions of order N with any denominators prime to N. -/
theorem rational_label {N : Nat} (odd : N%2=1) (m u n : Int) (l l' : Rat)
    (cross : fractionError N (l-l'))
    (first : fractionError N ((m:Rat)*l-2*(u:Rat)))
    (second : fractionError N (((m:Rat)-2)*l'-2*((u:Rat)-(n:Rat)))) :
    (N:Int)∣(l-(n:Rat)).num ∧ (l-(n:Rat)).den.Coprime N :=
  (fraction_iff_canonical _).mp (subtract_errors (fractionModule N odd) m u n l l' cross first second)

end IndependentIndices
