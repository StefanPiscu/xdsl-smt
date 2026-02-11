from xdsl.ir import Operation, SSAValue, Block
from xdsl.pattern_rewriter import PatternRewriter

from xdsl.dialects.riscv import IntRegisterType
from xdsl.dialects.builtin import IntegerType, Signedness

from xdsl_smt.semantics.riscv_semantics import *
from xdsl_smt.passes.lower_to_smt.smt_lowerer import SMTLowerer

SMTLowerer.type_lowerers = {
    IntegerType: ImmTypeSemantics(),
    IntRegisterType: IntRegisterTypeSemantics(),
}

def lower_block_args(block : Block) :
    for index, arg in enumerate(block.args): 
        new_type = SMTLowerer.lower_type(arg.type)
        new_arg = arg.block.insert_arg(new_type, index)
        arg.replace_by(new_arg)
        arg.block.erase_arg(arg)


def rdrsrs_int_op_smt(
        riscv_op_type : type[Operation], 
    ) -> tuple[Block, Sequence[SSAValue]]:
        mock_op = riscv_op_type.create(result_types=[IntRegisterType.unallocated()])
        block = Block(ops=[mock_op], arg_types=(IntRegisterType.unallocated(), IntRegisterType.unallocated()))
        rewriter = PatternRewriter(mock_op)
        lower_block_args(block)
        rhs, lhs = block.args
        new_res, _ = riscv_semantics[riscv_op_type].get_semantics(
            [lhs, rhs],
            [IntRegisterType.unallocated()], 
            {}, 
            None, 
            rewriter
        )
        rewriter.replace_matched_op([], new_res)
        return block, new_res

def rdrsimm_int_op_smt(
        riscv_op_type : type[Operation], 
        width : int
    ) -> tuple[Block, Sequence[SSAValue]]:
        mock_op = riscv_op_type.create(result_types=[IntRegisterType.unallocated()])
        # The lean definitions I'm using have the immediate as the first argument
        block = Block(ops=[mock_op], arg_types=(IntegerType(width, Signedness.SIGNED), IntRegisterType.unallocated()))
        lower_block_args(block)

        rewriter = PatternRewriter(mock_op)
        imm, a0 = block.args
        new_res, _ = riscv_semantics[riscv_op_type].get_semantics(
            [a0],
            [IntRegisterType.unallocated()], 
            {"immediate" : imm}, 
            None, 
            rewriter
        )
        rewriter.replace_matched_op([], new_res)
        return block, new_res
