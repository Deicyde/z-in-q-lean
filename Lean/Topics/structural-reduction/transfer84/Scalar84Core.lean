import Child84Patch
import PhysicalScalar

namespace StructuralReduction.Transfer84
open CircuitTransport

/-- Physical slot numbers start at one. A witness contains exactly 84 rationals. -/
def cell (x : Fin 84 → Rat) (n : Nat) : Rat :=
  if h : 0<n ∧ n≤84 then x ⟨n-1,by omega⟩ else 0

/-- Embed just the common and scalar parent coordinates. -/
def pull (x : Fin 84 → Rat) (n : Nat) : Rat :=
  if n≤17 then cell x n else if 123≤n ∧ n≤134 then cell x (n-105) else 0

def prefix84 (fallback : Nat→Op) : List Op :=
  List.ofFn (fun i : Fin 9918=>patch fallback i.val)

def program84 (fallback : Nat→Op) : List Op := prefix84 fallback ++ Output.suffix

theorem entry {i : Nat} {op : Op} (fallback : Nat→Op) (bound : i<9918)
    (eq : patch fallback i=op) : (program84 fallback)[i]?=some op := by
  have len : (prefix84 fallback).length=9918 := List.length_ofFn
  have small : i<(prefix84 fallback).length := by rw [len];exact bound
  rw [program84,List.getElem?_append_left small,prefix84,
      List.getElem?_ofFn,dif_pos bound,eq]

abbrev childWire (fallback : Nat→Op) (x : Fin 84→Rat) (i : Nat) :=
  valueAt (program84 fallback) (cell x) i

def parentFallback : Nat → Wires.Op := fun _=>.int 0

abbrev parentWire (x : Fin 84 → Rat) (i : Nat) :=
  Wires.read (Wires.complete parentFallback) (pull x) i

theorem signed84 (fallback : Nat→Op) (x : Fin 84→Rat) :
    (childWire fallback x 9980=0 ↔ ∀ j∈Output.wireList,childWire fallback x j=0) ∧
    (childWire fallback x 9981=0 ↔ cell x 1=0 ∨ ∀ j∈Output.wireList,childWire fallback x j=0) := by
  have length : (prefix84 fallback).length=9918 := List.length_ofFn
  have atZero : (prefix84 fallback)[0]?=some (.var 1) := by
    rw [prefix84,List.getElem?_ofFn,dif_pos (by decide : 0<9918)]
    rfl
  exact Output.signed_outputs (prefix84 fallback) length atZero (cell x)

end StructuralReduction.Transfer84
