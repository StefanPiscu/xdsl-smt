from xdsl.dialects import riscv
from xdsl_smt.dialects import smt_bitvector_dialect as smt_bv

from xdsl_smt.semantics.riscv_semantics import *
from riscv_instructions_smt import *
from lean_printer import print_lean_theorem

def print_theorem(name : str, semantics : tuple[Block, Sequence[SSAValue]]):
    block, res = semantics 
    print_lean_theorem(name, block, res)

print_theorem("add", trivial_rdrsrs_int_op_smt(riscv.AddOp, smt_bv.AddOp))
print_theorem("or", trivial_rdrsrs_int_op_smt(riscv.OrOp, smt_bv.OrOp))
print_theorem("xor", trivial_rdrsrs_int_op_smt(riscv.XorOp, smt_bv.XorOp))
print_theorem("and", trivial_rdrsrs_int_op_smt(riscv.AndOp, smt_bv.AndOp))
	
print_theorem("addi", trivial_rdrsimm_int_op_smt(riscv.AddiOp, smt_bv.AddOp, 12))
print_theorem("andi", trivial_rdrsimm_int_op_smt(riscv.AndiOp, smt_bv.AndOp, 12))
print_theorem("ori", trivial_rdrsimm_int_op_smt(riscv.OriOp, smt_bv.OrOp, 12))
print_theorem("xori", trivial_rdrsimm_int_op_smt(riscv.XoriOp, smt_bv.XorOp, 12))

print_theorem("slt", rdrsrs_int_op_smt(riscv.SltOp, slt_semantics))
