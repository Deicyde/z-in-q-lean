import TriClosed
import DetectorProjection
import QuadraticPivots

namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular
open Triangular.Data

/-- Slots of the 130-coordinate programs, in one-based parent numbering. -/
def parentSlots : List Nat := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,82,83,84,85,86,87,92,93,98,99,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,122,123,124,125,126,127,128,129,135,136,143,144,147,148,155,156,159,160,167,168,170,171,172,173,174,176,177]

def compactSlot (i : Nat) := parentSlots.idxOf i + 1

def seed130 (y : Fin 130→Rat) (i : Nat) : Rat := finiteLift y (compactSlot i)

def preliminary (g : Bool) (y : Fin 130→Rat) : Assignment := recov (ps g) (seed130 y)

inductive DBlock | one | two | three deriving DecidableEq,Repr

def detectors := [DBlock.one,.two,.three]

def DBlock.e : DBlock→Nat | .one=>135 | .two=>147 | .three=>159

def DBlock.den : DBlock→Rat | .one=>1 | .two=>19131876 | .three=>16

def DBlock.t (k : DBlock) (x : Assignment) : Rat := match k with
  | .one => 1-x 32 | .two => 1-4*x 145 | .three => 1-x 32-32*x 157

def DBlock.sl (k : DBlock) (pre base : Assignment) := 1-base k.e*(k.den*k.t pre)*base (k.e+1)

def DBlock.a (k : DBlock) (base : Assignment) := -(k.den*base k.e*base (k.e+1))^3

def DBlock.q (k : DBlock) (base : Assignment) := (base k.e)^19*k.a base

def DBlock.bigQ (k : DBlock) (pre base : Assignment) := (base k.e)^79*k.a base + k.sl pre base*base (k.e+1)

def DBlock.guard (k : DBlock) (pre base : Assignment) := base k.e*k.sl pre base

def detectorSeed (pre base : Assignment) (i : Nat) : Rat :=
  if i=136 then DBlock.one.a base else
  if i=140 then DBlock.one.q base else
  if i=141 then DBlock.one.bigQ pre base else
  if i=148 then DBlock.two.a base else
  if i=152 then DBlock.two.q base else
  if i=153 then DBlock.two.bigQ pre base else
  if i=160 then DBlock.three.a base else
  if i=164 then DBlock.three.q base else
  if i=165 then DBlock.three.bigQ pre base else
  base i

def middle (g : Bool) (y : Fin 130→Rat) : Assignment :=
  recov (ps g) (detectorSeed (preliminary g y) (seed130 y))

def guardValues (g : Bool) (y : Fin 130→Rat) : List Rat :=
  detectors.map fun k => k.guard (preliminary g y) (seed130 y)

inductive PPair | one | two | three | four deriving DecidableEq,Repr

def pairs := [PPair.one,.two,.three,.four]

def PPair.xslot : PPair→Nat | .one=>76 | .two=>86 | .three=>92 | .four=>98

def PPair.slot : PPair→Nat | .one=>80 | .two=>90 | .three=>96 | .four=>102

def PPair.rid : PPair→Nat | .one=>673 | .two=>677 | .three=>681 | .four=>685

def PPair.f : PPair→Polynomial | .one=>p673 | .two=>p677 | .three=>p681 | .four=>p685

def PPair.g : PPair→Polynomial | .one=>p674 | .two=>p678 | .three=>p682 | .four=>p686

def PPair.w0 (k : PPair) (z : Assignment) := 11*z k.xslot-24*z (k.xslot+1)
def PPair.w1 (k : PPair) (z : Assignment) := 22*z (k.xslot+1)-6*z k.xslot

def PPair.A (k : PPair) (z : Assignment) := 480675*CircuitTransport.Quadratic.g0 (k.w0 z) (k.w1 z)

def PPair.B (k : PPair) (z : Assignment) := 480675*CircuitTransport.Quadratic.g1 (k.w0 z) (k.w1 z)

def PPair.det (k : PPair) (z : Assignment) := k.A z*k.A z-(2*k.B z)*k.B z

def PPair.blank (k : PPair) (z : Assignment) := put (put z k.slot 0) (k.slot+1) 0

def PPair.U (k : PPair) (z : Assignment) :=
  (2*k.B z*value (k.blank z) k.g-k.A z*value (k.blank z) k.f)/k.det z

def PPair.V (k : PPair) (z : Assignment) :=
  (k.B z*value (k.blank z) k.f-k.A z*value (k.blank z) k.g)/k.det z

def fillPairs (z : Assignment) (i : Nat) : Rat :=
  if i=80 then PPair.one.U z else
  if i=81 then PPair.one.V z else
  if i=90 then PPair.two.U z else
  if i=91 then PPair.two.V z else
  if i=96 then PPair.three.U z else
  if i=97 then PPair.three.V z else
  if i=102 then PPair.four.U z else
  if i=103 then PPair.four.V z else
  z i

def chartPoint (g : Bool) (y : Fin 130→Rat) : Assignment := fillPairs (middle g y)

def parentRows (g : Bool) := Triangular.parent (ps g) (top::rest g)

def detIds := [304,521,544,545,546,526,354,528,550,551,552,533,404,535,556,557,558,540]
def pairIds := [673,674,677,678,681,682,685,686]
def peakIds := [335,385,435]
def activeRows (g : Bool) := (top::rest g).filter (fun r => !(detIds++pairIds).contains r.1)
def peakRows (g : Bool) := (activeRows g).filter (fun r => peakIds.contains r.1)
def rowsHold (rows : Rows) (z : Assignment) := ∀ r∈rows, value z r.2=0

def unmarked (g : Bool) (y : Fin 130→Rat) := rowsHold (activeRows g) (chartPoint g y) ∧ ∀ v∈guardValues g y, v=0

def chart (g marked : Bool) (y : Fin 130→Rat) : Prop :=
  if marked then rowsHold (peakRows g) (chartPoint g y) ∧ (finiteLift y 1=0 ∨ unmarked g y) else unmarked g y

theorem pair_det_ne (k : PPair) (z : Assignment) : k.det z≠0 :=
  CircuitTransport.Quadratic.physical_pade_det (z k.xslot) (z (k.xslot+1))

end PhysicalProjection
