from xdsl.dialects import riscv
from xdsl_smt.dialects import smt_bitvector_dialect as smt_bv

from xdsl_smt.semantics.riscv_semantics import *
from riscv_instructions_smt import *
from lean_printer import print_lean_theorem

def print_theorem(name : str, semantics : tuple[Block, Sequence[SSAValue]]):
    block, res = semantics 
    print_lean_theorem(name, block, res)

print_theorem("add", rdrsrs_int_op_smt(riscv.AddOp, smt_bv.AddOp))
print_theorem("or", rdrsrs_int_op_smt(riscv.OrOp, smt_bv.OrOp))
print_theorem("xor", rdrsrs_int_op_smt(riscv.XorOp, smt_bv.XorOp))
print_theorem("and", rdrsrs_int_op_smt(riscv.AndOp, smt_bv.AndOp))
	
print_theorem("addi", rdrsimm_int_op_smt(riscv.AddiOp, smt_bv.AddOp, 12))
	
