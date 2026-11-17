import JointWindows

/-! Construction of the actual nine affine preimages used to evaluate the
six scalar coefficients and sixteen ordinary tests, for one chosen h. -/
namespace Sun28.RealWindows
open Set NumberField ZInQ ZInQ.Mult Sun28.RealRatio Sun28.Scalar Sun28.Ordinary Sun28.Forward
open Sun28.FixedPreparation Sun28.WitnessIndices
noncomputable section

/-- A positive comparison index, with the four given odd root labels, has
actual rational affine preimages for all nine points satisfying the point guards. -/
theorem affine_inputs_for_indices (M : ℕ) (positive : 0<M) (six : 6∣M)
    (anchor q h : ℤ) (qn : q≠0) (hn : h≠0) (bn : h-anchor≠0)
    (n : Fin 4→ℤ) (s : n 1-1=(M:ℤ)*q) (odd : ∀ j,Odd (n j)) :
    ∃ A : Fin 9→AffineInput, Consequences (nineAffine A).doubles M anchor
      ⟨q,h,n,fun i=>h*n i⟩ := by
  classical
  let idx : Fin 9→ℤ := ![q,n 0,n 2,n 3,h,h*n 0,h*n 1,h*n 2,h*n 3]
  choose A original using fun i=>affine_double_surjective (idx i)
  let w := (nineAffine A).doubles
  let l : Labels := ⟨q,h,n,fun i=>h*n i⟩
  have Q : w.Q=q • P := original 0
  have H : w.H=h • P := original 4
  have N : w.N=n 0 • P := original 1
  have T : w.T=n 2 • P := original 2
  have Z : w.Z=n 3 • P := original 3
  have eqS : n 1=1+(M:ℤ)*q := by omega
  have R : Represents w M l := by
    refine ⟨Q.symm,H.symm,?_,?_⟩
    · intro i
      fin_cases i
      · exact N.symm
      · change n 1 • P=P+M • w.Q
        rw [Q,eqS,add_zsmul,one_zsmul,mul_smul]
        rfl
      · exact T.symm
      · exact Z.symm
    · intro i
      fin_cases i
      · exact (original 5).symm
      · exact (original 6).symm
      · exact (original 7).symm
      · exact (original 8).symm
  have nz (m : ℤ) (hm : m≠0) : m • P≠0 :=
    fun e=>hm (index_injective (e.trans (zero_zsmul P).symm))
  have bh : translatedBase w anchor=(h-anchor) • P := by
    rw [translatedBase,H,sub_eq_add_neg,←sub_zsmul]
  refine ⟨A,derive R ⟨Q ▸ nz _ qn,H ▸ nz _ hn,bh ▸ nz _ bn,?_,?_,?_⟩ positive six⟩
  · exact N ▸ chart_of_odd (odd 0)
  · exact T ▸ chart_of_odd (odd 2)
  · exact Z ▸ chart_of_odd (odd 3)

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalAddGroup G]

/-- For arbitrary integer input and fixed odd target roots, construct the
rational affine preimages with the same h on every signed CRT progression.
0<D and M|D allow D to contain every required small-prime multiple. -/
theorem choose_affine_windows (a : Orbit G) (model : ParameterModel a) (anchor : ℤ)
    (M D : ℕ) (positive : 0<M) (six : 6∣M) (dpos : 0<D) (dil : M∣D) (cmin : ℤ) :
    ∃ (c q : ℤ), (D:ℤ)∣c ∧ max cmin 0<c ∧ c=(M:ℤ)*q ∧
    ∀ (n : Fin 4→ℤ) (β : ℚ), n 1-1=c → (∀ i,Odd (n i)) → ∃ C : ℝ,1≤C ∧
    ∀ (h₀ : ℤ) (L : ℕ),0<L → ∀ (bad : Set ℤ),bad.Finite → ∀ hmin : ℤ,
    ∃ (h : ℤ) (k : ℕ) (A : Fin 9→AffineInput),
      h=h₀+(L:ℤ)*k ∧ max (max anchor hmin) 0<h ∧ h∉bad ∧
      let w:=(nineAffine A).doubles
      Consequences w M anchor ⟨q,h,n,fun i=>h*n i⟩ ∧
      (∀ i,|scalarEntries w M i|≤1) ∧
      (truncAt w.H≠0 ∧ conjugation (truncAt (translatedBase w anchor))≠0) ∧
      (∀ i,∀ σ : K0 →+* ℝ, |σ (ordinaryAt w M anchor β i)|≤C) ∧
      ∀ i,∀ ν : InfinitePlace K0, ν (ordinaryAt w M anchor β i)≤C := by
  obtain ⟨_,_,first⟩:=choose_shared_readouts a model anchor
  obtain ⟨c,u,cu,cp,_,later⟩:=first D dpos cmin
  obtain ⟨v,vd⟩:=dil
  let q : ℤ:=(v:ℤ)*u
  have cq : c=(M:ℤ)*q := by rw [cu,vd];push_cast;ring
  have qn : q≠0 := by intro eq; rw [eq,mul_zero] at cq;omega
  refine ⟨c,q,⟨u,cu⟩,cp,cq,?_⟩
  intro n β scalar odds
  obtain ⟨C,one,choose⟩:=later n β
  refine ⟨C,one,?_⟩
  intro h₀ L lp bad fb hm
  obtain ⟨h,k,eq,late,out,ratio,_,all⟩:=choose h₀ L lp bad fb hm
  obtain ⟨A,rep⟩:=affine_inputs_for_indices M positive six anchor q h qn (by omega) (by omega)
    n (scalar.trans cq) odds
  refine ⟨h,k,A,eq,late,out,rep,?_⟩
  exact shared_point_bounds rep scalar rfl (fun i=>rfl) β C ratio (fun i=>(all i).1)

end
end Sun28.RealWindows
#print axioms Sun28.RealWindows.affine_inputs_for_indices
#print axioms Sun28.RealWindows.choose_affine_windows
