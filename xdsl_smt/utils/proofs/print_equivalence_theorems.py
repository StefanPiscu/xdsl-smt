from xdsl.dialects import riscv

from xdsl_smt.semantics.riscv_semantics import *
from riscv_instructions_smt import *
from lean_printer import print_lean_theorem

def print_theorem(name : str, semantics : tuple[Block, Sequence[SSAValue]]):
    block, res = semantics 
    print_lean_theorem(name, block, res)

rdrsrs : Sequence[type[Operation]] = [ 
    riscv.AddOp,
    riscv.AddwOp,
    riscv.SubOp,
    riscv.SubwOp,
    riscv.OrOp,
    riscv.XorOp,
    riscv.AndOp,
    riscv.SltOp,
    riscv.SltuOp,
    riscv.SllOp,
    riscv.SllwOp,
    riscv.SrlOp,
    riscv.SrlwOp,
    riscv.SraOp,
    riscv.SrawOp,
]

rdrsimm : Sequence[type[Operation]] = [
    riscv.AddiOp,
    riscv.AddiwOp,
    riscv.AndiOp,
    riscv.OriOp,
    riscv.XoriOp,
    riscv.SltiOp,
    riscv.SltiuOp,
]
rdrsshamt : Sequence[tuple[type[Operation], int]] = [
    (riscv.SlliOp, 6),
    (riscv.SlliwOp, 5),
    (riscv.SrliOp, 6),
    (riscv.SrliwOp, 5),
    (riscv.SraiOp, 6),
    (riscv.SraiwOp, 5),

]


for op_type in rdrsrs : 
    print_theorem(op_type.name[6:], rdrsrs_int_op_smt(op_type))

for op_type in rdrsimm : 
    print_theorem(op_type.name[6:], rdrsimm_int_op_smt(op_type, 12))

for op_type, width in rdrsshamt : 
    print_theorem(op_type.name[6:], rdrsimm_int_op_smt(op_type, width))

print_theorem("slliuw", rdrsimm_int_op_smt(riscv.SlliUwOp, 6))


