import CertificateIndices

/-! Outside the fixed primes four rational squareclasses detect all five contacts. -/
namespace Sun28.RelativeContacts
open Sun28.Ordinary Sun28.WitnessHeight
noncomputable section

def relativeForm (s η a : ℚ) : ℚ := s^2-a/η

private theorem contact_by_difference {p : ℕ} [hp : Fact p.Prime] {S : Finset ℕ}
    (out : p∉S) (good : ¬p∣separation) {t : ℚ} (off : t∉marks) :
    p∈contactPrimes S t ↔ ∃ a∈marks, 0<padicValRat p (t-a) ∧ Odd (padicValRat p (t-a)) := by
  rw [mem_contactPrimes,and_iff_right hp.out,and_iff_right out]
  have eqv (a : ℚ) (ha:a∈marks) := projective_contact_iff (p:=p) (t:=t)
    (fun e=>off (e ▸ ha)) (mark_denominator_unit good ha)
  constructor <;> rintro ⟨a,ha,h⟩
  · exact ⟨a,ha,(eqv a ha).mp h⟩
  · exact ⟨a,ha,(eqv a ha).mpr h⟩

private theorem mark_unit {p : ℕ} [Fact p.Prime] (good : ¬p∣separation) {a : ℚ}
    (ha : a∈marks) (an : a≠0) : padicValRat p a=0 := by
  have zero : (0:ℚ) ∈ insert 3 marks := by norm_num [marks]
  simpa using mark_difference_unit good (Finset.mem_insert_of_mem ha) zero an

theorem contact_iff_odd_relative {p : ℕ} [Fact p.Prime] {S : Finset ℕ} (out : p∉S)
    (good : ¬p∣separation) {s η : ℚ} (sn : s≠0) (en : η≠0) (off : s^2*η∉marks) :
    p∈contactPrimes S (s^2*η) ↔ ∃ a∈marks, a≠0 ∧ Odd (padicValRat p (relativeForm s η a)) := by
  set t:=s^2*η
  have tn : t≠0 := mul_ne_zero (pow_ne_zero 2 sn) en
  have zmem : (0:ℚ)∈marks := by norm_num [marks]
  have val : padicValRat p t=2*padicValRat p s+padicValRat p η := by
    dsimp [t]; rw [padicValRat.mul (pow_ne_zero 2 sn) en,padicValRat.pow]; norm_num
  have diff (a : ℚ) (ha:a∈marks) : t-a≠0 := sub_ne_zero.mpr (fun ex=>off (ex ▸ ha))
  have addDiff (a : ℚ) (ha:a∈marks) : t+-a≠0 := by simpa only [sub_eq_add_neg] using diff a ha
  have value (a : ℚ) (ha : a∈marks) :
      padicValRat p (relativeForm s η a)=padicValRat p (t-a)-padicValRat p η := by
    have ne : t-a≠0 := sub_ne_zero.mpr (fun ex=>off (ex ▸ ha))
    have eqn : relativeForm s η a=(t-a)/η := by dsimp [relativeForm,t];field_simp
    rw [eqn,padicValRat.div ne en]
  have sum_neg (a : ℚ) (ha : a∈marks) (an:a≠0) (v:padicValRat p t<0) :
      padicValRat p (t-a)=padicValRat p t := by
    have au := mark_unit good ha an
    rw [sub_eq_add_neg,padicValRat.add_eq_of_lt (addDiff a ha) tn
      (neg_ne_zero.mpr an) (by simpa [au] using v)]
  have sum_pos (a : ℚ) (ha : a∈marks) (an:a≠0) (v:0<padicValRat p t) :
      padicValRat p (t-a)=0 := by
    have au := mark_unit good ha an
    have ne : -a+t≠0 := by rw [add_comm]; exact addDiff a ha
    rw [sub_eq_add_neg,add_comm,padicValRat.add_eq_of_lt ne (neg_ne_zero.mpr an) tn
      (by simpa [au] using v),padicValRat.neg,au]
  rw [contact_by_difference out good off]
  rcases lt_trichotomy (padicValRat p t) 0 with neg|zero|pos
  · constructor
    · rintro ⟨a,ha,h,_⟩
      by_cases an:a=0
      · subst a; simp only [sub_zero] at h; omega
      · rw [sum_neg a ha an neg] at h; omega
    · rintro ⟨a,ha,an,k,e⟩; rw [value a ha,sum_neg a ha an neg] at e;omega
  · constructor
    · rintro ⟨a,ha,h,k,e⟩
      have an : a≠0 := by rintro rfl; simp only [sub_zero,zero,lt_self_iff_false] at h
      refine ⟨a,ha,an,k+padicValRat p s,?_⟩;rw [value a ha];omega
    · rintro ⟨a,ha,an,k,e⟩;rw [value a ha] at e
      have lb : 0≤padicValRat p (t-a) := by
        have ne : t+-a≠0 := addDiff a ha
        have ws:=padicValRat.min_le_padicValRat_add (p:=p) ne
        simpa [zero,mark_unit good ha an,sub_eq_add_neg] using ws
      refine ⟨a,ha,by omega,k-padicValRat p s,by omega⟩
  · constructor
    · rintro ⟨a,ha,h,k,e⟩
      have az : a=0 := by by_contra an;rw [sum_pos a ha an pos] at h;omega
      subst a;rw [sub_zero] at e
      have h1 : (-1:ℚ)∈marks := by norm_num [marks]
      refine ⟨-1,h1,by norm_num,-k+padicValRat p s-1,?_⟩
      rw [value _ h1,sum_pos _ h1 (by norm_num) pos];omega
    · rintro ⟨a,ha,an,k,e⟩;rw [value a ha,sum_pos a ha an pos] at e
      refine ⟨0,zmem,by simpa using pos,?_⟩
      rw [sub_zero]; exact ⟨padicValRat p s-k-1,by omega⟩

/-- Exactly the mixed odd support across the twelve rational entries. -/
theorem union_iff_odd_relative {p : ℕ} [Fact p.Prime] {S : Finset ℕ} (out : p∉S)
    (good : ¬p∣separation) (s : Fin 3→ℚ) {η : ℚ} (en : η≠0)
    (sn : ∀ i, s i≠0) (off : ∀ i, (s i)^2*η∉marks) :
    p∈contactUnion S (fun i=>(s i)^2*η) ↔
      ∃ i a, a∈marks ∧ a≠0 ∧ Odd (padicValRat p (relativeForm (s i) η a)) := by
  constructor
  · intro mem
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp mem
    obtain ⟨a,ha,an,odd⟩:=(contact_iff_odd_relative out good (sn i) en (off i)).mp hi
    exact ⟨i,a,ha,an,odd⟩
  · rintro ⟨i,a,ha,an,odd⟩
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,(contact_iff_odd_relative out good
      (sn i) en (off i)).mpr ⟨a,ha,an,odd⟩⟩

end
end Sun28.RelativeContacts
#print axioms Sun28.RelativeContacts.contact_iff_odd_relative
#print axioms Sun28.RelativeContacts.union_iff_odd_relative
