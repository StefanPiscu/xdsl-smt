import RiscvEquivalence.Instructions
import Std.Tactic.BVDecide

open RV64

def _add (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.add a0 a1) ;
  a2
theorem add_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.add a0 a1 = _add a0 a1 := by
  simp [RV64.add, _add]
  try bv_decide
def _or (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.or a0 a1) ;
  a2
theorem or_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.or a0 a1 = _or a0 a1 := by
  simp [RV64.or, _or]
  try bv_decide
def _xor (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.xor a0 a1) ;
  a2
theorem xor_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.xor a0 a1 = _xor a0 a1 := by
  simp [RV64.xor, _xor]
  try bv_decide
def _and (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.and a0 a1) ;
  a2
theorem and_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.and a0 a1 = _and a0 a1 := by
  simp [RV64.and, _and]
  try bv_decide
def _addi (a0 : BitVec 12) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.signExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.add a1 a2) ;
  a3
theorem addi_eq (a0 : BitVec 12) (a1 : BitVec 64) : RV64.addi a0 a1 = _addi a0 a1 := by
  simp [RV64.addi, _addi]
  try bv_decide
def _andi (a0 : BitVec 12) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.signExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.and a1 a2) ;
  a3
theorem andi_eq (a0 : BitVec 12) (a1 : BitVec 64) : RV64.andi a0 a1 = _andi a0 a1 := by
  simp [RV64.andi, _andi]
  try bv_decide
def _ori (a0 : BitVec 12) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.signExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.or a1 a2) ;
  a3
theorem ori_eq (a0 : BitVec 12) (a1 : BitVec 64) : RV64.ori a0 a1 = _ori a0 a1 := by
  simp [RV64.ori, _ori]
  try bv_decide
def _xori (a0 : BitVec 12) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.signExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.xor a1 a2) ;
  a3
theorem xori_eq (a0 : BitVec 12) (a1 : BitVec 64) : RV64.xori a0 a1 = _xori a0 a1 := by
  simp [RV64.xori, _xori]
  try bv_decide
def _slt (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : Bool := (BitVec.slt a1 a0) ;
  let a3 : BitVec 64 := 0 ;
  let a4 : BitVec 64 := 1 ;
  let a5 : BitVec 64 := (cond a2 a4 a3) ;
  a5
theorem slt_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.slt a0 a1 = _slt a0 a1 := by
  simp [RV64.slt, _slt]
  try bv_decide
