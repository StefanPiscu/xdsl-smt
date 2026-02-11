import RiscvEquivalence.Instructions
import Std.Tactic.BVDecide

open RV64

def _add (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.add a1 a0) ;
  a2
theorem add_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.add a0 a1 = _add a0 a1 := by
  unfold RV64.add _add
  bv_decide
def _addw (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 32 := (BitVec.extractLsb 31 0 a1) ;
  let a3 : BitVec 32 := (BitVec.extractLsb 31 0 a0) ;
  let a4 : BitVec 32 := (BitVec.add a2 a3) ;
  let a5 : BitVec 64 := (BitVec.signExtend 64 a4) ;
  a5
theorem addw_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.addw a0 a1 = _addw a0 a1 := by
  unfold RV64.addw _addw
  bv_decide
def _sub (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.sub a1 a0) ;
  a2
theorem sub_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.sub a0 a1 = _sub a0 a1 := by
  unfold RV64.sub _sub
  bv_decide
def _subw (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 32 := (BitVec.extractLsb 31 0 a1) ;
  let a3 : BitVec 32 := (BitVec.extractLsb 31 0 a0) ;
  let a4 : BitVec 32 := (BitVec.sub a2 a3) ;
  let a5 : BitVec 64 := (BitVec.signExtend 64 a4) ;
  a5
theorem subw_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.subw a0 a1 = _subw a0 a1 := by
  unfold RV64.subw _subw
  bv_decide
def _or (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.or a1 a0) ;
  a2
theorem or_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.or a0 a1 = _or a0 a1 := by
  unfold RV64.or _or
  bv_decide
def _xor (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.xor a1 a0) ;
  a2
theorem xor_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.xor a0 a1 = _xor a0 a1 := by
  unfold RV64.xor _xor
  bv_decide
def _and (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.and a1 a0) ;
  a2
theorem and_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.and a0 a1 = _and a0 a1 := by
  unfold RV64.and _and
  bv_decide
def _slt (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : Bool := (BitVec.slt a1 a0) ;
  let a3 : BitVec 64 := 0 ;
  let a4 : BitVec 64 := 1 ;
  let a5 : BitVec 64 := (cond a2 a4 a3) ;
  a5
theorem slt_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.slt a0 a1 = _slt a0 a1 := by
  unfold RV64.slt _slt
  bv_decide
def _sltu (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : Bool := (BitVec.ult a1 a0) ;
  let a3 : BitVec 64 := 0 ;
  let a4 : BitVec 64 := 1 ;
  let a5 : BitVec 64 := (cond a2 a4 a3) ;
  a5
theorem sltu_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.sltu a0 a1 = _sltu a0 a1 := by
  unfold RV64.sltu _sltu
  bv_decide
def _sll (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 6 := (BitVec.extractLsb 5 0 a0) ;
  let a3 : BitVec 64 := (BitVec.zeroExtend 64 a2) ;
  let a4 : BitVec 64 := (BitVec.shiftLeft a1 (BitVec.toNat a3)) ;
  a4
theorem sll_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.sll a0 a1 = _sll a0 a1 := by
  unfold RV64.sll _sll
  bv_decide
def _sllw (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 32 := (BitVec.extractLsb 31 0 a1) ;
  let a3 : BitVec 5 := (BitVec.extractLsb 4 0 a0) ;
  let a4 : BitVec 32 := (BitVec.zeroExtend 32 a3) ;
  let a5 : BitVec 32 := (BitVec.shiftLeft a2 (BitVec.toNat a4)) ;
  let a6 : BitVec 64 := (BitVec.signExtend 64 a5) ;
  a6
theorem sllw_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.sllw a0 a1 = _sllw a0 a1 := by
  unfold RV64.sllw _sllw
  bv_decide
def _srl (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 6 := (BitVec.extractLsb 5 0 a0) ;
  let a3 : BitVec 64 := (BitVec.zeroExtend 64 a2) ;
  let a4 : BitVec 64 := (BitVec.ushiftRight a1 (BitVec.toNat a3)) ;
  a4
theorem srl_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.srl a0 a1 = _srl a0 a1 := by
  unfold RV64.srl _srl
  bv_decide
def _srlw (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 32 := (BitVec.extractLsb 31 0 a1) ;
  let a3 : BitVec 5 := (BitVec.extractLsb 4 0 a0) ;
  let a4 : BitVec 32 := (BitVec.zeroExtend 32 a3) ;
  let a5 : BitVec 32 := (BitVec.ushiftRight a2 (BitVec.toNat a4)) ;
  let a6 : BitVec 64 := (BitVec.signExtend 64 a5) ;
  a6
theorem srlw_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.srlw a0 a1 = _srlw a0 a1 := by
  unfold RV64.srlw _srlw
  bv_decide
def _sra (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 6 := (BitVec.extractLsb 5 0 a0) ;
  let a3 : BitVec 64 := (BitVec.zeroExtend 64 a2) ;
  let a4 : BitVec 64 := (BitVec.sshiftRight a1 (BitVec.toNat a3)) ;
  a4
theorem sra_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.sra a0 a1 = _sra a0 a1 := by
  unfold RV64.sra _sra
  bv_decide
def _sraw (a0 : BitVec 64) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 32 := (BitVec.extractLsb 31 0 a1) ;
  let a3 : BitVec 5 := (BitVec.extractLsb 4 0 a0) ;
  let a4 : BitVec 32 := (BitVec.zeroExtend 32 a3) ;
  let a5 : BitVec 32 := (BitVec.sshiftRight a2 (BitVec.toNat a4)) ;
  let a6 : BitVec 64 := (BitVec.signExtend 64 a5) ;
  a6
theorem sraw_eq (a0 : BitVec 64) (a1 : BitVec 64) : RV64.sraw a0 a1 = _sraw a0 a1 := by
  unfold RV64.sraw _sraw
  bv_decide
def _addi (a0 : BitVec 12) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.signExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.add a1 a2) ;
  a3
theorem addi_eq (a0 : BitVec 12) (a1 : BitVec 64) : RV64.addi a0 a1 = _addi a0 a1 := by
  unfold RV64.addi _addi
  bv_decide
def _addiw (a0 : BitVec 12) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.signExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.add a1 a2) ;
  let a4 : BitVec 32 := (BitVec.extractLsb 31 0 a3) ;
  let a5 : BitVec 64 := (BitVec.signExtend 64 a4) ;
  a5
theorem addiw_eq (a0 : BitVec 12) (a1 : BitVec 64) : RV64.addiw a0 a1 = _addiw a0 a1 := by
  unfold RV64.addiw _addiw
  bv_decide
def _andi (a0 : BitVec 12) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.signExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.and a1 a2) ;
  a3
theorem andi_eq (a0 : BitVec 12) (a1 : BitVec 64) : RV64.andi a0 a1 = _andi a0 a1 := by
  unfold RV64.andi _andi
  bv_decide
def _ori (a0 : BitVec 12) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.signExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.or a1 a2) ;
  a3
theorem ori_eq (a0 : BitVec 12) (a1 : BitVec 64) : RV64.ori a0 a1 = _ori a0 a1 := by
  unfold RV64.ori _ori
  bv_decide
def _xori (a0 : BitVec 12) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.signExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.xor a1 a2) ;
  a3
theorem xori_eq (a0 : BitVec 12) (a1 : BitVec 64) : RV64.xori a0 a1 = _xori a0 a1 := by
  unfold RV64.xori _xori
  bv_decide
def _slti (a0 : BitVec 12) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.signExtend 64 a0) ;
  let a3 : Bool := (BitVec.slt a1 a2) ;
  let a4 : BitVec 64 := 0 ;
  let a5 : BitVec 64 := 1 ;
  let a6 : BitVec 64 := (cond a3 a5 a4) ;
  a6
theorem slti_eq (a0 : BitVec 12) (a1 : BitVec 64) : RV64.slti a0 a1 = _slti a0 a1 := by
  unfold RV64.slti _slti
  bv_decide
def _sltiu (a0 : BitVec 12) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.signExtend 64 a0) ;
  let a3 : Bool := (BitVec.ult a1 a2) ;
  let a4 : BitVec 64 := 0 ;
  let a5 : BitVec 64 := 1 ;
  let a6 : BitVec 64 := (cond a3 a5 a4) ;
  a6
theorem sltiu_eq (a0 : BitVec 12) (a1 : BitVec 64) : RV64.sltiu a0 a1 = _sltiu a0 a1 := by
  unfold RV64.sltiu _sltiu
  bv_decide
def _slli (a0 : BitVec 6) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.zeroExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.shiftLeft a1 (BitVec.toNat a2)) ;
  a3
theorem slli_eq (a0 : BitVec 6) (a1 : BitVec 64) : RV64.slli a0 a1 = _slli a0 a1 := by
  unfold RV64.slli _slli
  bv_decide
def _slliw (a0 : BitVec 5) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 32 := (BitVec.extractLsb 31 0 a1) ;
  let a3 : BitVec 32 := (BitVec.zeroExtend 32 a0) ;
  let a4 : BitVec 32 := (BitVec.shiftLeft a2 (BitVec.toNat a3)) ;
  let a5 : BitVec 64 := (BitVec.signExtend 64 a4) ;
  a5
theorem slliw_eq (a0 : BitVec 5) (a1 : BitVec 64) : RV64.slliw a0 a1 = _slliw a0 a1 := by
  unfold RV64.slliw _slliw
  bv_decide
def _srli (a0 : BitVec 6) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.zeroExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.ushiftRight a1 (BitVec.toNat a2)) ;
  a3
theorem srli_eq (a0 : BitVec 6) (a1 : BitVec 64) : RV64.srli a0 a1 = _srli a0 a1 := by
  unfold RV64.srli _srli
  bv_decide
def _srliw (a0 : BitVec 5) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 32 := (BitVec.extractLsb 31 0 a1) ;
  let a3 : BitVec 32 := (BitVec.zeroExtend 32 a0) ;
  let a4 : BitVec 32 := (BitVec.ushiftRight a2 (BitVec.toNat a3)) ;
  let a5 : BitVec 64 := (BitVec.signExtend 64 a4) ;
  a5
theorem srliw_eq (a0 : BitVec 5) (a1 : BitVec 64) : RV64.srliw a0 a1 = _srliw a0 a1 := by
  unfold RV64.srliw _srliw
  bv_decide
def _srai (a0 : BitVec 6) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.zeroExtend 64 a0) ;
  let a3 : BitVec 64 := (BitVec.sshiftRight a1 (BitVec.toNat a2)) ;
  a3
theorem srai_eq (a0 : BitVec 6) (a1 : BitVec 64) : RV64.srai a0 a1 = _srai a0 a1 := by
  unfold RV64.srai _srai
  bv_decide
def _sraiw (a0 : BitVec 5) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 32 := (BitVec.extractLsb 31 0 a1) ;
  let a3 : BitVec 32 := (BitVec.zeroExtend 32 a0) ;
  let a4 : BitVec 32 := (BitVec.sshiftRight a2 (BitVec.toNat a3)) ;
  let a5 : BitVec 64 := (BitVec.signExtend 64 a4) ;
  a5
theorem sraiw_eq (a0 : BitVec 5) (a1 : BitVec 64) : RV64.sraiw a0 a1 = _sraiw a0 a1 := by
  unfold RV64.sraiw _sraiw
  bv_decide
def _slliuw (a0 : BitVec 6) (a1 : BitVec 64) : BitVec 64 :=
  let a2 : BitVec 64 := (BitVec.zeroExtend 64 a0) ;
  let a3 : BitVec 32 := (BitVec.extractLsb 31 0 a1) ;
  let a4 : BitVec 64 := (BitVec.zeroExtend 64 a3) ;
  let a5 : BitVec 64 := (BitVec.shiftLeft a4 (BitVec.toNat a2)) ;
  a5
theorem slliuw_eq (a0 : BitVec 6) (a1 : BitVec 64) : RV64.slliuw a0 a1 = _slliuw a0 a1 := by
  unfold RV64.slliuw _slliuw
  bv_decide
