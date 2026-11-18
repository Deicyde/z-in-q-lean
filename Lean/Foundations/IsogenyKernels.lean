module

public import Std

@[expose] public section

namespace IsogenyKernels
open Lean.Grind

/-- Signed exponents of the fixed prime basis, reduced modulo two. -/
structure Squareclass where
  sign : Fin 2
  p2 : Fin 2
  p5 : Fin 2
  p7 : Fin 2
  p11 : Fin 2
  p13 : Fin 2
  p17 : Fin 2
  p37 : Fin 2
  p73 : Fin 2
  p109 : Fin 2
  p131 : Fin 2
  p317 : Fin 2
  p1277 : Fin 2
  p59929 : Fin 2
  p322269869512007 : Fin 2

structure PsiFree where
  sign : Fin 2
  p5 : Fin 2
  p7 : Fin 2
  p11 : Fin 2
  p13 : Fin 2
  p17 : Fin 2
  p37 : Fin 2
  p109 : Fin 2
  p131 : Fin 2
  p59929 : Fin 2

def psiLocal (x : Squareclass) : Prop :=
  x.p2 = 0 ∧
  x.p2 + x.p11 + x.p13 + x.p17 + x.p37 + x.p109 + x.p317 = 0 ∧
  x.sign + x.p2 + x.p17 + x.p37 + x.p73 + x.p131 + x.p1277 = 0 ∧
  x.sign + x.p2 + x.p7 + x.p13 + x.p17 + x.p73 + x.p109 + x.p131 + x.p322269869512007 = 0 ∧
  x.p2 + x.p7 + x.p13 + x.p17 + x.p37 + x.p73 + x.p317 + x.p1277 + x.p322269869512007 = 0

def psiRestrict (x : Squareclass) : PsiFree :=
  ⟨x.sign, x.p5, x.p7, x.p11, x.p13, x.p17, x.p37, x.p109, x.p131, x.p59929⟩

def psiExtend (f : PsiFree) : Squareclass where
  sign := f.sign
  p2 := 0
  p5 := f.p5
  p7 := f.p7
  p11 := f.p11
  p13 := f.p13
  p17 := f.p17
  p37 := f.p37
  p73 := f.p11 + f.p13 + f.p37
  p109 := f.p109
  p131 := f.p131
  p317 := f.p11 + f.p13 + f.p17 + f.p37 + f.p109
  p1277 := f.sign + f.p11 + f.p13 + f.p17 + f.p131
  p59929 := f.p59929
  p322269869512007 := f.sign + f.p7 + f.p11 + f.p17 + f.p37 + f.p109 + f.p131

theorem psi_free (f : PsiFree) : psiRestrict (psiExtend f) = f := by
  cases f
  rfl

theorem psi_kernel (x : Squareclass) :
    psiLocal x ↔ psiExtend (psiRestrict x) = x := by
  rcases x with ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
  simp only [psiLocal, psiExtend, psiRestrict, Squareclass.mk.injEq]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    repeat' apply And.intro
    all_goals first | rfl | grobner
  · rintro ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩
    repeat' apply And.intro
    all_goals grobner

theorem psi_image (f : PsiFree) : psiLocal (psiExtend f) := by
  apply (psi_kernel _).2
  rw [psi_free]

structure PhiFree where
  p59929 : Fin 2

def phiLocal (x : Squareclass) : Prop :=
  x.sign = 0 ∧
  x.p2 = 0 ∧
  x.p7 = 0 ∧
  x.p13 = 0 ∧
  x.p17 = 0 ∧
  x.p37 = 0 ∧
  x.p73 = 0 ∧
  x.p2 + x.p5 + x.p13 + x.p17 + x.p109 = 0 ∧
  x.p2 + x.p5 + x.p7 + x.p37 + x.p131 = 0 ∧
  x.sign + x.p5 + x.p7 + x.p37 + x.p73 + x.p131 = 0 ∧
  x.p317 = 0 ∧
  x.p2 + x.p5 + x.p13 + x.p17 + x.p109 + x.p317 = 0 ∧
  x.p2 + x.p11 + x.p13 + x.p17 + x.p37 + x.p109 + x.p317 = 0 ∧
  x.p2 + x.p5 + x.p7 + x.p11 + x.p37 + x.p73 + x.p109 + x.p317 = 0 ∧
  x.p2 + x.p5 + x.p7 + x.p11 + x.p13 + x.p37 + x.p73 + x.p109 + x.p317 = 0 ∧
  x.p5 + x.p7 + x.p11 + x.p37 + x.p73 + x.p109 + x.p131 + x.p317 = 0 ∧
  x.p5 + x.p7 + x.p11 + x.p17 + x.p37 + x.p73 + x.p109 + x.p131 + x.p317 = 0 ∧
  x.p1277 = 0 ∧
  x.sign + x.p2 + x.p17 + x.p37 + x.p73 + x.p1277 = 0 ∧
  x.p2 + x.p5 + x.p7 + x.p37 + x.p131 + x.p1277 = 0 ∧
  x.sign + x.p5 + x.p13 + x.p17 + x.p73 + x.p131 + x.p1277 = 0 ∧
  x.sign + x.p5 + x.p7 + x.p13 + x.p17 + x.p73 + x.p131 + x.p1277 = 0 ∧
  x.p322269869512007 = 0 ∧
  x.sign + x.p7 + x.p11 + x.p131 + x.p322269869512007 = 0 ∧
  x.sign + x.p2 + x.p7 + x.p11 + x.p131 + x.p322269869512007 = 0 ∧
  x.p5 + x.p7 + x.p11 + x.p13 + x.p17 + x.p131 + x.p322269869512007 = 0 ∧
  x.p5 + x.p7 + x.p11 + x.p13 + x.p17 + x.p73 + x.p131 + x.p322269869512007 = 0 ∧
  x.sign + x.p5 + x.p7 + x.p37 + x.p73 + x.p131 + x.p322269869512007 = 0 ∧
  x.sign + x.p2 + x.p7 + x.p11 + x.p13 + x.p17 + x.p73 + x.p109 + x.p131 + x.p322269869512007 = 0 ∧
  x.p2 + x.p5 + x.p13 + x.p17 + x.p109 + x.p131 + x.p1277 + x.p322269869512007 = 0 ∧
  x.p2 + x.p5 + x.p13 + x.p17 + x.p37 + x.p109 + x.p131 + x.p1277 + x.p322269869512007 = 0 ∧
  x.p2 + x.p7 + x.p13 + x.p17 + x.p37 + x.p73 + x.p317 + x.p1277 + x.p322269869512007 = 0

def phiRestrict (x : Squareclass) : PhiFree :=
  ⟨x.p59929⟩

def phiExtend (f : PhiFree) : Squareclass where
  sign := 0
  p2 := 0
  p5 := 0
  p7 := 0
  p11 := 0
  p13 := 0
  p17 := 0
  p37 := 0
  p73 := 0
  p109 := 0
  p131 := 0
  p317 := 0
  p1277 := 0
  p59929 := f.p59929
  p322269869512007 := 0

theorem phi_free (f : PhiFree) : phiRestrict (phiExtend f) = f := by
  cases f
  rfl

theorem phi_kernel (x : Squareclass) :
    phiLocal x ↔ phiExtend (phiRestrict x) = x := by
  rcases x with ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
  simp only [phiLocal, phiExtend, phiRestrict, Squareclass.mk.injEq]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
    repeat' apply And.intro
    all_goals first | rfl | grobner
  · rintro ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩
    repeat' apply And.intro
    all_goals grobner

theorem phi_image (f : PhiFree) : phiLocal (phiExtend f) := by
  apply (phi_kernel _).2
  rw [phi_free]

#print axioms psi_free
#print axioms psi_kernel
#print axioms psi_image
#print axioms phi_free
#print axioms phi_kernel
#print axioms phi_image
end IsogenyKernels
