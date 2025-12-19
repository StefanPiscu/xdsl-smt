from typing import Sequence, Mapping, Callable
from dataclasses import dataclass
from xdsl.ir import Attribute, Operation, SSAValue
from xdsl.utils.hints import isa
from xdsl.dialects.builtin import IntegerAttr, IntegerType
from xdsl.pattern_rewriter import PatternRewriter
from xdsl_smt.semantics.semantics import (
    TypeSemantics,
	OperationSemantics,
    AttributeSemantics,
)

from xdsl_smt.dialects import smt_bitvector_dialect as smt_bv
from xdsl_smt.dialects import smt_dialect as smt
from xdsl.dialects.riscv import IntRegisterType
import xdsl.dialects.riscv as riscv

WORD_SIZE = 64

class IntRegisterTypeSemantics(TypeSemantics):
    """Convert an integer register type to a bitvector integer"""
    def get_semantics(self, type: Attribute):
        assert isinstance(type, IntRegisterType)
        return smt_bv.BitVectorType(WORD_SIZE)

class ImmTypeSemantics(TypeSemantics):
    """Convert the type of an immediate to a bitvector of the right size"""
    def get_semantics(self, type: Attribute):
        assert isinstance(type, IntegerType)
        return smt_bv.BitVectorType(type.width)

class ImmSemantics(AttributeSemantics):
    """Convert an immediate attribute to a bitvector of the right size"""
    def get_semantics(self, attribute: Attribute, rewriter: PatternRewriter):
        assert isa(attribute, IntegerAttr[IntegerType])
        op = smt_bv.ConstantOp(attribute.value, attribute.type.width)
        rewriter.insert_op_before_matched_op(op)
        return op.res


@dataclass
class TrivialRdRsRsIntSemantics(OperationSemantics):
    riscv_op_type: type[Operation]
    smt_op_type: type[Operation]

    def get_semantics(
        self,
        operands: Sequence[SSAValue],
        results: Sequence[Attribute],
        attributes: Mapping[str, Attribute | SSAValue],
				effect_state: SSAValue | None,
        rewriter: PatternRewriter,
    ) -> tuple[Sequence[SSAValue], SSAValue | None]:
        assert isinstance(results[0], IntRegisterType)
        new_op = self.smt_op_type.create(
            operands=operands,
            result_types=[smt_bv.BitVectorType(WORD_SIZE)],
        )
        rewriter.insert_op_before_matched_op([new_op])
        return ([new_op.results[0]], effect_state)

@dataclass
class RdRsRsIntSemantics(OperationSemantics):
    semantics: Callable[[SSAValue, SSAValue, PatternRewriter], Sequence[SSAValue]]

    def get_semantics(
        self,
        operands: Sequence[SSAValue],
        results: Sequence[Attribute],
        attributes: Mapping[str, Attribute | SSAValue],
				effect_state: SSAValue | None,
        rewriter: PatternRewriter,
    ) -> tuple[Sequence[SSAValue], SSAValue | None]:
        assert isinstance(results[0], IntRegisterType)
        new_results = self.semantics(operands[0], operands[1], rewriter)
        return (new_results, effect_state)

def ofBool(val : SSAValue, rewriter : PatternRewriter) -> SSAValue:
    zero = smt_bv.ConstantOp(0, 64)
    one = smt_bv.ConstantOp(1, 64)
    iteOp = smt.IteOp(val, one.res, zero.res) 
    rewriter.insert_op_before_matched_op([zero, one, iteOp])
    return iteOp.res

def slt_semantics(rs1 : SSAValue, rs2 : SSAValue, rewriter : PatternRewriter) -> Sequence[SSAValue]: 
    sltOp = smt_bv.SltOp(rs1, rs2)
    rewriter.insert_op_before_matched_op([sltOp])
    return [ofBool(sltOp.res, rewriter)]

@dataclass
class TrivialRdRsImmIntSemantics(OperationSemantics):
    riscv_op_type: type[Operation]
    smt_op_type: type[Operation]

    def get_semantics(
        self,
        operands: Sequence[SSAValue],
        results: Sequence[Attribute],
        attributes: Mapping[str, Attribute | SSAValue],
		effect_state: SSAValue | None,
        rewriter: PatternRewriter,
    ) -> tuple[Sequence[SSAValue], SSAValue | None]:
        assert isinstance(results[0], IntRegisterType)
        imm = attributes["immediate"]
        if isinstance(imm, Attribute):
            assert isinstance(imm, Attribute)
            imm = ImmSemantics().get_semantics(imm, rewriter)
        imm_extend = smt_bv.SignExtendOp(imm, smt_bv.BitVectorType(WORD_SIZE))
        op = self.smt_op_type.create(
            operands=[operands[0], imm_extend.results[0]],
            result_types=[smt_bv.BitVectorType(WORD_SIZE)]
        )
        rewriter.insert_op_before_matched_op([imm_extend, op])
        return ([op.results[0]], effect_state)

riscv_semantics: dict[type[Operation], OperationSemantics] = {
    riscv.AddOp : TrivialRdRsRsIntSemantics(riscv.AddOp, smt_bv.AddOp),
    riscv.SubOp : TrivialRdRsRsIntSemantics(riscv.SubOp, smt_bv.SubOp),
    riscv.XorOp : TrivialRdRsRsIntSemantics(riscv.XorOp, smt_bv.XorOp),
    riscv.AndOp : TrivialRdRsRsIntSemantics(riscv.AndOp, smt_bv.AndOp),
    riscv.OrOp : TrivialRdRsRsIntSemantics(riscv.OrOp, smt_bv.OrOp),

    riscv.AddiOp : TrivialRdRsImmIntSemantics(riscv.AddiOp, smt_bv.AddOp),
    riscv.XoriOp : TrivialRdRsImmIntSemantics(riscv.XoriOp, smt_bv.XorOp),
    riscv.AndiOp : TrivialRdRsImmIntSemantics(riscv.AndiOp, smt_bv.AndOp),
    riscv.OriOp : TrivialRdRsImmIntSemantics(riscv.OriOp, smt_bv.OrOp),

    riscv.SltOp: RdRsRsIntSemantics(slt_semantics),
}