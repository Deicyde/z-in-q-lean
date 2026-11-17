import PaperSexticSigns

/-! Geometric points in both charts are the actual weighted-projective quotient.
Classical genus-two coordinate transformations reduce to its two explicit maps. -/
namespace ZInQBlueprint.MarkedForm
open CurveChart
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- Every isomorphism formula on a short genus-two equation has this shape
(Voight, Quaternion Algebras, §43.3, (43.3.3)). -/
structure Lift (u : ℚ) (δ : K) where
  lin : (K×K) ≃ₗ[K] (K×K)
  unitY : Kˣ
  equation : ∀ p, paperForm u δ (lin p)=(unitY:K)^2*paperForm u δ p

def Lift.action {u : ℚ} {δ : K} (t : Lift u δ) : Equiv.Perm (Points (paperForm u δ)) :=
  coordinateEquiv t.lin t.unitY t.equation

def negY (F : K×K → K) : Equiv.Perm (Points F) :=
  coordinateEquiv (LinearEquiv.refl K _) (-1 : Kˣ) (fun p => by simp)

omit [CharZero K] in
/-- The coefficients of the linear equivalence in the standard basis. -/
theorem base_matrix (g : (K×K) ≃ₗ[K] (K×K)) :
    ∃ a b c d : K, a*d-b*c≠0 ∧ ∀ x z, g (x,z)=(a*x+b*z,c*x+d*z) := by
  let a := (g (1,0)).1
  let b := (g (0,1)).1
  let c := (g (1,0)).2
  let d := (g (0,1)).2
  have form (x z:K) : g (x,z)=(a*x+b*z,c*x+d*z) := by
    have spl : (x,z)=x • ((1,0):K×K)+z • ((0,1):K×K) := by ext <;> simp
    rw [spl,map_add,map_smul,map_smul]
    ext <;> simp [a,b,c,d,mul_comm]
  refine ⟨a,b,c,d,?_,form⟩
  intro h
  have z : g (d,-c)=0 := by
    rw [form]
    apply Prod.ext <;> dsimp
    · linear_combination h
    · ring
  have zx := g.injective (z.trans g.map_zero.symm)
  have hc : c=0 := by simpa using congrArg Prod.snd zx
  have hd : d=0 := by simpa using congrArg Prod.fst zx
  obtain ⟨⟨u,v⟩,hs⟩ := g.surjective (0,1)
  rw [form,hc,hd] at hs
  simpa using congrArg Prod.snd hs

/-- Coordinate rigidity, including points above infinity, with a single global sign. -/
theorem lift_action_sign [Infinite K] {u : ℚ} (hu : u∉ZInQ.contactSet) {δ : K} (hd : δ≠0)
    (t : Lift u δ) : t.action=Equiv.refl _ ∨ t.action=negY (paperForm u δ) := by
  obtain ⟨a,b,c,d,hm,hlin⟩ := base_matrix t.lin
  have hact (x z : K) :
      paperForm u δ (a*x+b*z,c*x+d*z)=(t.unitY:K)^2*paperForm u δ (x,z) := by
    rw [←hlin x z]; exact t.equation _
  obtain ⟨hb,hc,ha,hn,he⟩ := paper_matrix_signs hu hd hm hact
  subst b; subst c; subst d
  let v : Kˣ := Units.mk0 a hn
  have linear (p:K×K) : t.lin p=v • p := by
    rcases p with ⟨x,z⟩
    rw [hlin]
    ext <;> simp [v,Units.smul_def]
  rcases he with he | he
  · left
    apply Equiv.ext
    intro p
    induction p using Quotient.inductionOn with
    | _ p =>
      obtain ⟨q,hq,hb,hy⟩ := coordinateEquiv_coordinates t.lin t.unitY t.equation p
      change coordinateEquiv _ _ _ _=Quotient.mk _ p
      rw [hq]
      apply Eq.symm
      apply Quotient.sound
      exact ⟨v,hb.trans (linear p.base),by rw [hy,he]; rfl⟩
  · right
    apply Equiv.ext
    intro p
    induction p using Quotient.inductionOn with
    | _ p =>
      obtain ⟨q,hq,hb,hy⟩ := coordinateEquiv_coordinates t.lin t.unitY t.equation p
      have hneg (z:K×K) : paperForm u δ ((LinearEquiv.refl K _) z)=
          ((-1:Kˣ):K)^2*paperForm u δ z := by simp
      obtain ⟨r,hr,hrb,hry⟩ := coordinateEquiv_coordinates (LinearEquiv.refl K _) (-1:Kˣ) hneg p
      change coordinateEquiv _ _ _ _=coordinateEquiv (LinearEquiv.refl K _) (-1:Kˣ) hneg _
      rw [hq,hr]
      apply Eq.symm
      apply Quotient.sound
      refine ⟨v,?_,?_⟩
      · rw [hrb,hb]; exact linear _
      · rw [hry,hy,he]; simp [v]

end
end ZInQBlueprint.MarkedForm
#print axioms ZInQBlueprint.MarkedForm.base_matrix
#print axioms ZInQBlueprint.MarkedForm.lift_action_sign
