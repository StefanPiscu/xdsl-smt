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


def regToWord(val: SSAValue, rewriter: PatternRewriter) -> SSAValue:
    extractOp = smt_bv.ExtractOp(val, WORD_SIZE//2-1, 0)
    rewriter.insert_op_before_matched_op(extractOp)
    return extractOp.res

def extendTo(val: SSAValue, width : int, rewriter: PatternRewriter, sign : bool = True) -> SSAValue:
    if sign:
        extendOp = smt_bv.SignExtendOp(val, smt_bv.BitVectorType(width))
    else:
        extendOp = smt_bv.ZeroExtendOp(val, smt_bv.BitVectorType(width))
    rewriter.insert_op_before_matched_op(extendOp)
    return extendOp.res

def wordToReg(val: SSAValue, rewriter: PatternRewriter) -> SSAValue:
    return extendTo(val, WORD_SIZE, rewriter) 

def regToShamt(val: SSAValue, rewriter: PatternRewriter, shamt: int = 6) -> SSAValue:
    extractOp = smt_bv.ExtractOp(val, shamt-1, 0)
    rewriter.insert_op_before_matched_op(extractOp)
    return extractOp.res

def ofBool(val : SSAValue, rewriter : PatternRewriter) -> SSAValue:
    zero = smt_bv.ConstantOp(0, WORD_SIZE)
    one = smt_bv.ConstantOp(1, WORD_SIZE)
    iteOp = smt.IteOp(val, one.res, zero.res) 
    rewriter.insert_op_before_matched_op([zero, one, iteOp])
    return iteOp.res

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

@dataclass
class RdRsRsIntWordSemantics(OperationSemantics):
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
        rs1 = regToWord(operands[0], rewriter)
        rs2 = regToWord(operands[1], rewriter)
        temp_results = self.semantics(rs1, rs2, rewriter)
        new_results = [wordToReg(temp_results[0], rewriter)]
        return (new_results, effect_state)

@dataclass 
class RdRsImmIntSemantics(OperationSemantics):
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
        imm = attributes["immediate"]
        if isinstance(imm, Attribute):
            assert isinstance(imm, Attribute)
            imm = ImmSemantics().get_semantics(imm, rewriter)
        imm = extendTo(imm, WORD_SIZE, rewriter)
        new_results = self.semantics(operands[0], imm, rewriter)
        return (new_results, effect_state)
        
@dataclass
class RdRsImmIntWordSemantics(OperationSemantics):
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
        imm = attributes["immediate"]
        if isinstance(imm, Attribute):
            assert isinstance(imm, Attribute)
            imm = ImmSemantics().get_semantics(imm, rewriter)
        imm = extendTo(imm, WORD_SIZE, rewriter)
        temp_results = self.semantics(operands[0], imm, rewriter)
        trunc_res = regToWord(temp_results[0], rewriter)
        new_results = [wordToReg(trunc_res, rewriter)]
        return (new_results, effect_state)


@dataclass
class RdRsRsShamtSemantics(OperationSemantics):
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
        shamt = regToShamt(operands[1], rewriter)
        shamt = extendTo(shamt, WORD_SIZE, rewriter, False)
        new_results = self.semantics(operands[0], shamt, rewriter)
        return (new_results, effect_state)

@dataclass
class RdRsRsShamtWordSemantics(OperationSemantics):
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
        rs1 = regToWord(operands[0], rewriter)
        shamt = regToShamt(operands[1], rewriter, 5)
        shamt = extendTo(shamt, WORD_SIZE//2, rewriter, False)
        temp_results = self.semantics(rs1, shamt, rewriter)
        new_results = [wordToReg(temp_results[0], rewriter)]
        return (new_results, effect_state)


@dataclass 
class RdRsShamtSemantics(OperationSemantics):
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
        shamt = attributes["immediate"]
        if isinstance(shamt, Attribute):
            assert isinstance(shamt, Attribute)
            shamt = ImmSemantics().get_semantics(shamt, rewriter)
        shamt = extendTo(shamt, WORD_SIZE, rewriter, False)
        new_results = self.semantics(operands[0], shamt, rewriter)
        return (new_results, effect_state)

@dataclass 
class RdRsShamtWordSemantics(OperationSemantics):
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
        shamt = attributes["immediate"]
        if isinstance(shamt, Attribute):
            assert isinstance(shamt, Attribute)
            shamt = ImmSemantics().get_semantics(shamt, rewriter)
        rs1 = regToWord(operands[0], rewriter)
        shamt = extendTo(shamt, WORD_SIZE//2, rewriter, False)
        temp_results = self.semantics(rs1, shamt, rewriter)
        new_results = [wordToReg(temp_results[0], rewriter)]
        return (new_results, effect_state)

def trivial_binary_semantics(op_type : type[smt_bv.BinaryBVOp]
    ) -> Callable[[SSAValue, SSAValue, PatternRewriter], Sequence[SSAValue]]:
    def semantics(operand1 : SSAValue, operand2: SSAValue, rewriter: PatternRewriter) -> Sequence[SSAValue]:
        op = op_type(operand1, operand2)
        rewriter.insert_op_before_matched_op(op)
        return [op.res]
    return semantics

def cmp_semantics(op_type: type[smt_bv.BinaryPredBVOp]):
    def semantics(rs1 : SSAValue, rs2 : SSAValue, rewriter : PatternRewriter) -> Sequence[SSAValue]: 
        cmpOp = op_type(rs1, rs2)
        rewriter.insert_op_before_matched_op([cmpOp])
        return [ofBool(cmpOp.res, rewriter)]
    return semantics


add_semantics = trivial_binary_semantics(smt_bv.AddOp)

sll_semantics = trivial_binary_semantics(smt_bv.ShlOp)
srl_semantics = trivial_binary_semantics(smt_bv.LShrOp)
sra_semantics = trivial_binary_semantics(smt_bv.AShrOp)

def slliuw_semantics(rs : SSAValue, shamt : SSAValue, rewriter : PatternRewriter) -> Sequence[SSAValue]:
    trunc = regToWord(rs, rewriter)
    zero_ext = smt_bv.ZeroExtendOp(trunc, smt_bv.BitVectorType(64)) 
    shift = smt_bv.ShlOp(zero_ext.res, shamt)
    rewriter.insert_op_before_matched_op([zero_ext, shift])
    return [shift.res]

riscv_semantics: dict[type[Operation], OperationSemantics] = {
    riscv.AddOp : RdRsRsIntSemantics(add_semantics),
    riscv.AddiOp : RdRsImmIntSemantics(add_semantics),
    riscv.AddwOp : RdRsRsIntWordSemantics(add_semantics),
    riscv.AddiwOp : RdRsImmIntWordSemantics(add_semantics),

    riscv.SubOp : RdRsRsIntSemantics(trivial_binary_semantics(smt_bv.SubOp)),
    riscv.SubwOp : RdRsRsIntWordSemantics(trivial_binary_semantics(smt_bv.SubOp)),

    riscv.XorOp : RdRsRsIntSemantics(trivial_binary_semantics(smt_bv.XorOp)),
    riscv.AndOp : RdRsRsIntSemantics(trivial_binary_semantics(smt_bv.AndOp)),
    riscv.OrOp : RdRsRsIntSemantics(trivial_binary_semantics(smt_bv.OrOp)),

    riscv.XoriOp : RdRsImmIntSemantics(trivial_binary_semantics(smt_bv.XorOp)),
    riscv.AndiOp : RdRsImmIntSemantics(trivial_binary_semantics(smt_bv.AndOp)),
    riscv.OriOp : RdRsImmIntSemantics(trivial_binary_semantics(smt_bv.OrOp)),

    riscv.SltOp: RdRsRsIntSemantics(cmp_semantics(smt_bv.SltOp)),
    riscv.SltiOp: RdRsImmIntSemantics(cmp_semantics(smt_bv.SltOp)),
    riscv.SltuOp: RdRsRsIntSemantics(cmp_semantics(smt_bv.UltOp)),
    riscv.SltiuOp: RdRsImmIntSemantics(cmp_semantics(smt_bv.UltOp)),

    riscv.SllOp: RdRsRsShamtSemantics(sll_semantics),
    riscv.SlliOp: RdRsShamtSemantics(sll_semantics),
    riscv.SllwOp: RdRsRsShamtWordSemantics(sll_semantics),
    riscv.SlliwOp: RdRsShamtWordSemantics(sll_semantics),
    riscv.SlliUwOp: RdRsShamtSemantics(slliuw_semantics),
    
    riscv.SrlOp: RdRsRsShamtSemantics(srl_semantics),
    riscv.SrliOp: RdRsShamtSemantics(srl_semantics),
    riscv.SrlwOp: RdRsRsShamtWordSemantics(srl_semantics),
    riscv.SrliwOp: RdRsShamtWordSemantics(srl_semantics),

    riscv.SraOp: RdRsRsShamtSemantics(sra_semantics),
    riscv.SraiOp: RdRsShamtSemantics(sra_semantics),
    riscv.SrawOp: RdRsRsShamtWordSemantics(sra_semantics),
    riscv.SraiwOp: RdRsShamtWordSemantics(sra_semantics),
}